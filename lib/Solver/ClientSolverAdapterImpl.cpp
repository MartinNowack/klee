/*
 * STPProcessSolver.cpp
 *
 *  Created on: Aug 20, 2015
 *      Author: seadmin
 */
/***/

#include "klee/Solver.h"
#include "klee/SolverImpl.h"
#include "klee/SolverStats.h"

#include "klee/util/SharedMemory.h"
#include "klee/util/Serialization.h"

// TODO clean me up
#include "STPBuilder.h"
#include "MetaSMTBuilder.h"

#include "klee/Constraints.h"
#include "klee/Expr.h"
#include "klee/TimerStatIncrementer.h"
#include "klee/util/Assignment.h"
#include "klee/util/ExprPPrinter.h"
#include "klee/util/ExprUtil.h"
#include "klee/Internal/Support/Timer.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/CommandLine.h"

#include <cassert>
#include <cstdio>
#include <map>
#include <vector>

#include <errno.h>
#include <unistd.h>
#include <signal.h>
#include <sys/wait.h>
#include <sys/ipc.h>
#include <sys/shm.h>

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/ErrorHandling.h"
#include "llvm/Support/FileSystem.h"
#include "llvm/Support/Path.h"

#include <thread>
#include <limits.h>

using namespace klee;
extern bool IgnoreSolverFailures;

std::string do_readlink(std::string const &path) {
  char buff[PATH_MAX];
  ssize_t len = ::readlink(path.c_str(), buff, sizeof(buff) - 1);
  if (len != -1) {
    buff[len] = '\0';
    return std::string(buff);
  }
  /* handle error condition */
  return "";
}

std::string findSolverExecutable() {

#ifdef KLEE_TOOLDIR
  {
    auto path = std::string(KLEE_TOOLDIR) + "/solver-sa";
    if (llvm::sys::fs::exists(path))
      return path;
  }
#endif

#ifdef KLEE_INSTALL_BIN_DIR
  {
    auto path = std::string(KLEE_INSTALL_BIN_DIR) + "/solver-sa";
    if (llvm::sys::fs::exists(path))
      return path;
  }
#endif

  /// FIXME This is too linux specific
  std::string p = do_readlink("/proc/self/exe");
  if (p.empty())
    klee_error("Couldn't retrieve path of own executable");

  llvm::SmallVector<char, 16> Path(p.begin(), p.end());
  llvm::sys::path::remove_filename(Path);
  llvm::sys::path::append(Path, "solver-sa");
  auto solverPath = llvm::StringRef(Path.data(), Path.size());

  // Check if file is available in same directory as calling executable
  if (llvm::sys::fs::exists(solverPath))
    return solverPath;
  // Try to find with automatic path resolution
  return "solver-sa";
}

class ClientSolverAdapterImpl : public SolverImpl {
private:
  double timeout;
  SolverRunStatus runStatusCode;
  int processPid;
  std::string shared_mem_id;
  std::unique_ptr<SharedMem> smem_request;
  std::unique_ptr<SharedMem> smem_response;

  Serializer serializer;
  Deserializer deserializer;

  void startProcess() {
    // fork process here
    auto solverPath = findSolverExecutable();
    processPid = fork();
    if (processPid == -1) {
      klee_error(RuntimeSolver, "Fork failed for ClientSolverAdapter");
    }
    if (processPid == 0) {
      char *argv[] = {const_cast<char *>(solverPath.data()),
                      const_cast<char *>(shared_mem_id.c_str()),
		      const_cast<char *>(std::to_string(CoreSolverToUse.getValue()).c_str()), nullptr};
      execvp(argv[0], &argv[0]);
      klee_error(RuntimeSolver, "Execvp() failed %s", strerror(errno));
    }
  }

  void killProcess() {
    if (processPid > 0) {
      int res_wpid = 0;
      do {
        kill(processPid, SIGKILL);
        int status;
        res_wpid = waitpid(processPid, &status, WNOHANG);
      } while (res_wpid != -1 && errno != ECHILD);
      processPid = -1;
    }
  }

  void prepareRequest(SharedMem::command command) {
    runStatusCode = SOLVER_RUN_STATUS_FAILURE;
    smem_request->setCommand(command);
  }

  bool requestResult() {
    // Signal server
    smem_request->signal(SharedMem::CONSUMER);
    auto wait_timeout = (timeout ? timeout : 5);
    // wait anyway for a timeout, we have to check for liveness of the process
    while (!smem_request->waitTimeout(SharedMem::PRODUCER, wait_timeout)) {
      int status;
      auto res_wpid = waitpid(processPid, &status, WNOHANG);

      assert(res_wpid != (pid_t)-1);

      // Check if process is still there
      if (res_wpid == 0) {
        // if no timeout was specified, continue to wait
        if (!timeout) {
          continue;
        }
        runStatusCode = SOLVER_RUN_STATUS_TIMEOUT;
      } else {
        // Something happened
        runStatusCode = SOLVER_RUN_STATUS_UNEXPECTED_EXIT_CODE;
        if (IgnoreSolverFailures)
          klee_warning("Solver terminated unexpectedly");
        else
          klee_error(RuntimeSolver, "Solver terminated unexpectedly");
      }
      killProcess();

      // Reset memory and synchronization status
      smem_request->clearMemory();
      smem_response->clearMemory();

      smem_request->resetSync();
      smem_response->resetSync();

      startProcess();
      return false;
    }
    return true;
  }

public:
  ClientSolverAdapterImpl(ArrayCache *cache, bool _optimizeDivides = true)
      : timeout(0), runStatusCode(SolverRunStatus::SOLVER_RUN_STATUS_FAILURE),
        processPid(-1),
        shared_mem_id("klee_" + std::to_string(getpid()) + "_" +
                      std::to_string(std::hash<std::thread::id>()(
                          std::this_thread::get_id()))),
        smem_request(
            new SharedMem(SharedMem::defaultSize, shared_mem_id + "_request")),
        smem_response(
            new SharedMem(SharedMem::defaultSize, shared_mem_id + "_response")),
        serializer(*smem_request), deserializer(*smem_response, cache) {
    // fork process here
    startProcess();
  }
  ~ClientSolverAdapterImpl() {
    if (processPid > 0) {
      smem_request->signalExit();
      int status;
      waitpid(processPid, &status, 0);
    }
    killProcess();
  }

  char *getConstraintLog(const Query &query) override {
    TimerStatIncrementer t(stats::queryTime);

    // Acquire lock on the shared memory
    SharedMem::Locker lock(*smem_request);
    prepareRequest(SharedMem::CONSTRAINT_LOG);
    std::vector<const Array *> no_additional_arrays;
    serializer.serializeQuery(query, no_additional_arrays);

    ++stats::queries;
    ++stats::queryCounterexamples;

    auto result = requestResult();

    assert(result);

    return deserializer.deserializeConstraintLogAnswer();
  }

  void setCoreSolverTimeout(double _timeout) override { timeout = _timeout; }

  bool computeTruth(const Query &query, bool &isValid) override {
    TimerStatIncrementer t(stats::queryTime);

    // Request ownership of the shared memory
    SharedMem::Locker lock(*smem_request);

    prepareRequest(SharedMem::COMPUTE_TRUTH);
    std::vector<const Array *> no_additional_arrays;
    serializer.serializeQuery(query, no_additional_arrays);

    ++stats::queries;
    ++stats::queryCounterexamples;

    if (!requestResult())
      return false;

    bool success;
    deserializer.deserializeComputeTruthAnswer(isValid, success);
    return success;
  }

  bool computeValidity(const Query &query, Solver::Validity &result) override {
    TimerStatIncrementer t(stats::queryTime);

    // Request ownership of the shared memory
    SharedMem::Locker lock(*smem_request);

    prepareRequest(SharedMem::COMPUTE_VALIDITY);
    std::vector<const Array *> no_additional_arrays;
    serializer.serializeQuery(query, no_additional_arrays);

    ++stats::queries;
    ++stats::queryCounterexamples;

    if (!requestResult())
      return false;

    bool success;
    deserializer.deserializeComputeValidityAnswer(result, success);
    return success;
  }

  bool computeValue(const Query &query, ref<Expr> &result) override {
    TimerStatIncrementer t(stats::queryTime);

    // Request ownership of the shared memory
    SharedMem::Locker lock(*smem_request);

    prepareRequest(SharedMem::COMPUTE_VALUE);
    std::vector<const Array *> no_additional_arrays;
    serializer.serializeQuery(query, no_additional_arrays);

    ++stats::queries;
    ++stats::queryCounterexamples;

    if (!requestResult())
      return false;

    bool success;
    deserializer.deserializeComputeValueAnswer(result, success);
    return success;
  }

  bool computeInitialValues(const Query &query,
                            const std::vector<const Array *> &objects,
                            std::vector<std::vector<unsigned char> > &values,
                            bool &hasSolution) override {
    TimerStatIncrementer t(stats::queryTime);

    // Request ownership of the shared memory
    SharedMem::Locker lock(*smem_request);
    prepareRequest(SharedMem::INITIAL_VALUE);

    serializer.serializeQuery(query, objects);
    ++stats::queries;
    ++stats::queryCounterexamples;

    if (!requestResult())
      return false;

    bool success;
    deserializer.deserializeComputeInitialValuesAnswer(
        values, success, hasSolution, runStatusCode);

    if (success) {
      if (hasSolution)
        ++stats::queriesInvalid;
      else
        ++stats::queriesValid;
    }

    return success;
  }

  SolverRunStatus getOperationStatusCode() override { return runStatusCode; }
};

/***/

ClientProcessAdapterSolver::ClientProcessAdapterSolver(ArrayCache *cache,
                                                       bool optimizeDivides)
    : Solver(new ClientSolverAdapterImpl(cache, optimizeDivides)) {}

char *ClientProcessAdapterSolver::getConstraintLog(const Query &query) {
  return impl->getConstraintLog(query);
}

void ClientProcessAdapterSolver::setCoreSolverTimeout(double timeout) {
  impl->setCoreSolverTimeout(timeout);
}
