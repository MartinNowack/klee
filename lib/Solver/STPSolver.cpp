//===-- STPSolver.cpp -----------------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#include "klee/Config/config.h"
#ifdef ENABLE_STP
#include "STPBuilder.h"
#include "klee/Solver.h"
#include "klee/SolverImpl.h"
#include "klee/Constraints.h"
#include "klee/Internal/Support/ErrorHandling.h"
#include "klee/util/Assignment.h"
#include "klee/util/ExprUtil.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/Errno.h"
#include "llvm/Support/ErrorHandling.h"

#include <errno.h>
#include <unistd.h>
#include <signal.h>
#include <sys/wait.h>
#include <sys/ipc.h>
#include <sys/shm.h>

bool IgnoreSolverFailures;
namespace {

llvm::cl::opt<bool> DebugDumpSTPQueries(
    "debug-dump-stp-queries", llvm::cl::init(false),
    llvm::cl::desc("Dump every STP query to stderr (default=off)"));

llvm::cl::opt<bool, true> IgnoreSolverFailuresCmd(
    "ignore-solver-failures",
    llvm::cl::desc("Ignore any solver failures (default=off)"),
    llvm::cl::location(IgnoreSolverFailures), llvm::cl::init(false));
}

#define vc_bvBoolExtract IAMTHESPAWNOFSATAN

static unsigned char *shared_memory_ptr;
static int shared_memory_id = 0;
// Darwin by default has a very small limit on the maximum amount of shared
// memory, which will quickly be exhausted by KLEE running its tests in
// parallel. For now, we work around this by just requesting a smaller size --
// in practice users hitting this limit on counterexample sizes probably already
// are hitting more serious scalability issues.
#ifdef __APPLE__
static const unsigned shared_memory_size = 1 << 16;
#else
static const unsigned shared_memory_size = 1 << 20;
#endif

static void stp_error_handler(const char *err_msg) {
  fprintf(stderr, "error: STP Error: %s\n", err_msg);
  abort();
}

namespace klee {

class STPSolverImpl : public SolverImpl {
private:
  VC vc;
  STPBuilder *builder;
  double timeout;
  bool useForkedSTP;
  SolverRunStatus runStatusCode;
  uint64_t stackIndex;
  bool incremental;

public:
  STPSolverImpl(bool _useForkedSTP, bool _optimizeDivides = true);
  ~STPSolverImpl();

  char *getConstraintLog(const Query &);
  void setCoreSolverTimeout(double _timeout) { timeout = _timeout; }

  bool computeTruth(const Query &, bool &isValid);
  bool computeValue(const Query &, ref<Expr> &result);
  bool computeInitialValues(const Query &,
                            const std::vector<const Array *> &objects,
                            std::vector<std::vector<unsigned char> > &values,
                            bool &hasSolution);
  bool computePartialInitialValues(
      const Query &, const std::vector<const Array *> &objects,
      std::vector<std::vector<unsigned char> > &values, bool &hasSolution);
  void popStack(size_t index);

  SolverRunStatus getOperationStatusCode();
  void setIncrementalStatus(bool enable);
  bool getIncrementalStatus();

  void clearSolverStack();
};

STPSolverImpl::STPSolverImpl(bool _useForkedSTP, bool _optimizeDivides)
    : vc(vc_createValidityChecker()),
      builder(new STPBuilder(vc, _optimizeDivides)), timeout(0.0),
      useForkedSTP(_useForkedSTP), runStatusCode(SOLVER_RUN_STATUS_FAILURE),
      stackIndex(0), incremental(false) {
  assert(vc && "unable to create validity checker");
  assert(builder && "unable to create STPBuilder");

  // In newer versions of STP, a memory management mechanism has been
  // introduced that automatically invalidates certain C interface
  // pointers at vc_Destroy time.  This caused double-free errors
  // due to the ExprHandle destructor also attempting to invalidate
  // the pointers using vc_DeleteExpr.  By setting EXPRDELETE to 0
  // we restore the old behaviour.
  vc_setInterfaceFlags(vc, EXPRDELETE, 0);

  make_division_total(vc);

  vc_registerErrorHandler(::stp_error_handler);

  if (useForkedSTP) {
    assert(shared_memory_id == 0 && "shared memory id already allocated");
    shared_memory_id =
        shmget(IPC_PRIVATE, shared_memory_size, IPC_CREAT | 0700);
    if (shared_memory_id < 0)
      klee_error("unable to allocate shared memory region");
    shared_memory_ptr = (unsigned char *)shmat(shared_memory_id, NULL, 0);
    if (shared_memory_ptr == (void *)-1)
      klee_error("unable to attach shared memory region");
    shmctl(shared_memory_id, IPC_RMID, NULL);
  }
}

STPSolverImpl::~STPSolverImpl() {
  // Detach the memory region.
  if (shared_memory_ptr)
    shmdt(shared_memory_ptr);
  shared_memory_ptr = 0;
  shared_memory_id = 0;

  delete builder;

  vc_Destroy(vc);
}

/***/

STPSolver::STPSolver(bool useForkedSTP, bool optimizeDivides)
    : Solver(new STPSolverImpl(useForkedSTP, optimizeDivides)) {}

char *STPSolver::getConstraintLog(const Query &query) {
  return impl->getConstraintLog(query);
}

void STPSolver::setCoreSolverTimeout(double timeout) {
  impl->setCoreSolverTimeout(timeout);
}

/***/

char *STPSolverImpl::getConstraintLog(const Query &query) {
  auto emptyConstraints = query.constraints.empty();
  if (!emptyConstraints) {
    vc_push(vc);
    ++stackIndex;
    for (std::vector<ref<Expr> >::const_iterator it = query.constraints.begin(),
                                                 ie = query.constraints.end();
         it != ie; ++it)
      vc_assertFormula(vc, builder->construct(*it));
  }

  assert(query.expr == ConstantExpr::alloc(0, Expr::Bool) &&
         "Unexpected expression in query!");

  char *buffer;
  unsigned long length;

  // New stack level for the query
  vc_push(vc);
  vc_printQueryStateToBuffer(vc, builder->getFalse(), &buffer, &length, false);
  vc_pop(vc);

  // Remove added constraints
  if (!incremental && !emptyConstraints) {
    vc_pop(vc);
    --stackIndex;
  }
  return buffer;
}

bool STPSolverImpl::computeTruth(const Query &query, bool &isValid) {
  std::vector<const Array *> objects;
  std::vector<std::vector<unsigned char> > values;
  bool hasSolution;

  if (!computeInitialValues(query, objects, values, hasSolution))
    return false;

  isValid = !hasSolution;
  return true;
}

bool STPSolverImpl::computeValue(const Query &query, ref<Expr> &result) {
  std::vector<const Array *> objects;
  std::vector<std::vector<unsigned char> > values;
  bool hasSolution;

  // Find the object used in the expression, and compute an assignment
  // for them.
  findSymbolicObjects(query.expr, objects);
  if (!computeInitialValues(query.withFalse(), objects, values, hasSolution))
    return false;
  assert(hasSolution && "state has invalid constraint set");

  // Evaluate the expression with the computed assignment.
  Assignment a(objects, values);
  // We just compute any value, therefore the expression can be either true or
  // false
  // force concretization to acquire one possible outcome
  // Currently we assume that computeValue generates a constant
  result = a.evaluate(query.expr, true /* concretize symbolics */);

  return true;
}

static SolverImpl::SolverRunStatus
runAndGetCex(::VC vc, STPBuilder *builder, ::VCExpr q,
             const std::vector<const Array *> &objects,
             std::vector<std::vector<unsigned char> > &values,
             bool &hasSolution) {
  // XXX I want to be able to timeout here, safely
  hasSolution = !vc_query(vc, q);

  if (hasSolution) {
    values.reserve(objects.size());
    for (std::vector<const Array *>::const_iterator it = objects.begin(),
                                                    ie = objects.end();
         it != ie; ++it) {
      const Array *array = *it;
      std::vector<unsigned char> data;

      data.reserve(array->size);
      for (unsigned offset = 0; offset < array->size; offset++) {
        ExprHandle counter =
            vc_getCounterExample(vc, builder->getInitialRead(array, offset));
        unsigned char val = getBVUnsigned(counter);
        data.push_back(val);
      }

      values.push_back(data);
    }
  }

  if (true == hasSolution) {
    return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
  } else {
    return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
  }
}

static void stpTimeoutHandler(int x) { _exit(52); }

static SolverImpl::SolverRunStatus
runAndGetCexForked(::VC vc, STPBuilder *builder, ::VCExpr q,
                   const std::vector<const Array *> &objects,
                   std::vector<std::vector<unsigned char> > &values,
                   bool &hasSolution, double timeout) {
  unsigned char *pos = shared_memory_ptr;
  unsigned sum = 0;
  for (std::vector<const Array *>::const_iterator it = objects.begin(),
                                                  ie = objects.end();
       it != ie; ++it)
    sum += (*it)->size;
  if (sum >= shared_memory_size)
    klee_error(RuntimeSolver, "not enough shared memory for counterexample");

  fflush(stdout);
  fflush(stderr);
  int pid = fork();
  if (pid == -1) {
    if (IgnoreSolverFailures)
      klee_warning("fork failed (for STP) - %s", llvm::sys::StrError(errno).c_str());
    else
      klee_error(RuntimeSolver, "fork failed (for STP) - %s", llvm::sys::StrError(errno).c_str());

    return SolverImpl::SOLVER_RUN_STATUS_FORK_FAILED;
  }

  if (pid == 0) {
    if (timeout) {
      ::alarm(0); /* Turn off alarm so we can safely set signal handler */
      ::signal(SIGALRM, stpTimeoutHandler);
      ::alarm(std::max(1, (int)timeout));
    }
    unsigned res = vc_query(vc, q);
    if (!res) {
      for (std::vector<const Array *>::const_iterator it = objects.begin(),
                                                      ie = objects.end();
           it != ie; ++it) {
        const Array *array = *it;
        for (unsigned offset = 0; offset < array->size; offset++) {
          ExprHandle counter =
              vc_getCounterExample(vc, builder->getInitialRead(array, offset));
          *pos++ = getBVUnsigned(counter);
        }
      }
    }
    _exit(res);
  } else {
    int status;
    pid_t res;

    do {
      res = waitpid(pid, &status, 0);
    } while (res < 0 && errno == EINTR);

    if (res < 0) {
      if (IgnoreSolverFailures)
        klee_warning("waitpid() for STP failed");
      else
        klee_error(RuntimeSolver, "waitpid() for STP failed");

      return SolverImpl::SOLVER_RUN_STATUS_WAITPID_FAILED;
    }

    // From timed_run.py: It appears that linux at least will on
    // "occasion" return a status when the process was terminated by a
    // signal, so test signal first.
    if (WIFSIGNALED(status) || !WIFEXITED(status)) {
      if (IgnoreSolverFailures)
        klee_warning("STP did not return successfully.  Most likely you forgot "
                     "to run 'ulimit -s unlimited'");
      else
        klee_error(RuntimeSolver,
                   "STP did not return successfully.  Most likely you forgot "
                   "to run 'ulimit -s unlimited'");

      return SolverImpl::SOLVER_RUN_STATUS_INTERRUPTED;
    }

    int exitcode = WEXITSTATUS(status);
    if (exitcode == 0) {
      hasSolution = true;
    } else if (exitcode == 1) {
      hasSolution = false;
    } else if (exitcode == 52) {
      klee_warning("STP timed out");
      // mark that a timeout occurred
      return SolverImpl::SOLVER_RUN_STATUS_TIMEOUT;
    } else {
      if (IgnoreSolverFailures)
        klee_warning("STP did not return a recognized code");
      else
        klee_error(RuntimeSolver, "STP did not return a recognized code");

      return SolverImpl::SOLVER_RUN_STATUS_UNEXPECTED_EXIT_CODE;
    }

    if (hasSolution) {
      values = std::vector<std::vector<unsigned char> >(objects.size());
      unsigned i = 0;
      for (std::vector<const Array *>::const_iterator it = objects.begin(),
                                                      ie = objects.end();
           it != ie; ++it) {
        const Array *array = *it;
        std::vector<unsigned char> &data = values[i++];
        data.insert(data.begin(), pos, pos + array->size);
        pos += array->size;
      }
    }

    if (true == hasSolution) {
      return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_SOLVABLE;
    } else {
      return SolverImpl::SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE;
    }
  }
}
bool STPSolverImpl::computeInitialValues(
    const Query &query, const std::vector<const Array *> &objects,
    std::vector<std::vector<unsigned char> > &values, bool &hasSolution) {
  assert(stackIndex == 0 || incremental);

  auto success =
      computePartialInitialValues(query, objects, values, hasSolution);

  if (!incremental) {
    clearSolverStack();
  }

  return success;
}

bool STPSolverImpl::computePartialInitialValues(
    const Query &query, const std::vector<const Array *> &objects,
    std::vector<std::vector<unsigned char> > &values, bool &hasSolution) {
  runStatusCode = SOLVER_RUN_STATUS_FAILURE;

  TimerStatIncrementer t(stats::queryTime);

  vc_push(vc);

  bool emptyConstraints = query.constraints.empty();
  if (incremental && !emptyConstraints) {
    vc_push(vc);
    ++stackIndex;

    for (ConstraintManager::const_iterator it = query.constraints.begin(),
                                           ie = query.constraints.end();
         it != ie; ++it) {
      vc_assertFormula(vc, builder->construct(*it));
    }
  }
  ++stats::queries;
  ++stats::queryCounterexamples;

  vc_push(vc);
  if (!incremental) {
    for (ConstraintManager::const_iterator it = query.constraints.begin(),
                                           ie = query.constraints.end();
         it != ie; ++it) {
      vc_assertFormula(vc, builder->construct(*it));
    }
  }
  ExprHandle stp_e = builder->construct(query.expr);
  if (DebugDumpSTPQueries) {
    char *buf;
    unsigned long len;
    vc_printQueryStateToBuffer(vc, stp_e, &buf, &len, false);
    klee_warning("STP query:\n%.*s\n", (unsigned)len, buf);
    free(buf);
  }

  bool success;
  if (useForkedSTP) {
    runStatusCode = runAndGetCexForked(vc, builder, stp_e, objects, values,
                                       hasSolution, timeout);
    success = ((SOLVER_RUN_STATUS_SUCCESS_SOLVABLE == runStatusCode) ||
               (SOLVER_RUN_STATUS_SUCCESS_UNSOLVABLE == runStatusCode));
  } else {
    runStatusCode =
        runAndGetCex(vc, builder, stp_e, objects, values, hasSolution);
    success = true;
  }

  vc_pop(vc);

  if (success) {
    if (hasSolution)
      ++stats::queriesInvalid;
    else
      ++stats::queriesValid;
  }

  return success;
}

void STPSolverImpl::popStack(size_t index) {
  for (;stackIndex > index; -- stackIndex) {
    vc_pop(vc);
  }
}

SolverImpl::SolverRunStatus STPSolverImpl::getOperationStatusCode() {
  return runStatusCode;
}

void STPSolverImpl::setIncrementalStatus(bool enable) { incremental = enable; }

bool STPSolverImpl::getIncrementalStatus() { return incremental; }

void STPSolverImpl::clearSolverStack() {
  // remove every item from the stack
  popStack(0);
}
}
#endif // ENABLE_STP
