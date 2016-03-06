/*
 * ExpressionSerializer.cpp
 *
 *  Created on: Aug 14, 2015
 *      Author: Martin Nowack
 *
 * Provides stand-alone solver interface
 */
#include "klee/Solver.h"
#include "klee/SolverImpl.h"
#include "klee/Constraints.h"
#include "klee/util/ArrayCache.h"
#include "klee/util/SharedMemory.h"
#include "klee/util/Serialization.h"

#include <limits>
#include <sys/wait.h>
#include <unistd.h>

#include <fstream>

using namespace klee;

/*
 * Main idea: Solve request through shared memory.
 *
 * Important is that we can not hold the lock while
 * we are working on the request as this process might
 * misbehave/crash.
 *
 * Therefore we wait for signals to flag the current
 * stage for processing.
 * wait for signal CONSUMER: Waiting for a new request
 * After signal CONSUMER: We are the owner of the memory,
 *  do the hard work
 * After signal PRODUCER: We are not owner of the memory anymore
 */

int main(int argc, char **argv, char **envp) {

  // setup new shared mem for queries ...
  assert(argc == 2);

  // todo Use division argument as well
  ArrayCache cache;
//  Solver *coreSolver = klee::createCoreSolver(CoreSolverToUse, &cache);

//  Solver *coreSolver = new STPSolver(false, true);
  Solver *coreSolver = new Z3Solver();
//  Solver *coreSolver = new STPSolver(false, false);


  auto solver = coreSolver;

  // Take the ID from the first argument
  SharedMem request(SharedMem::defaultSize, std::string(argv[1]) + "_request");
  SharedMem response(SharedMem::defaultSize,
                     std::string(argv[1]) + "_response");

  auto parent_pid = getppid();
  Deserializer deserializer(request, &cache);
  Serializer serializer(response);

  auto FileName = "/proc/" + std::to_string(parent_pid) + "/status";

  // Wait for termination
  while (!request.exit()) {
    // Wait for request
    request.lock();
    if (!request.waitTimeout(SharedMem::CONSUMER, 5)) {
      request.unlock();

      // check if parent is still alive
      if (kill(parent_pid, 0) == -1)
        return 1;

      std::ifstream ifs(FileName);
      std::string str((std::istreambuf_iterator<char>(ifs)),
                      std::istreambuf_iterator<char>());
      if (str.find("zombie") != std::string::npos)
        return 0;

      continue;
    }
    if (request.exit()) {
      request.unlock();
      return 0;
    }
    request.unlock();

    switch (request.getCommand()) {
    case SharedMem::INITIAL_VALUE: {
      // Acquire query from shared memory
      ConstraintManager cm;
      std::vector<const Array *> arrays;
      auto query = deserializer.deserializeQuery(cm, arrays);
      std::vector<std::vector<unsigned char> > values;
      bool hasSolution = false;
      bool success = solver->impl->computeInitialValues(query, arrays, values,
                                                        hasSolution);

      serializer.serializeComputeInitialValuesAnswer(
          values, success, hasSolution, solver->impl->getOperationStatusCode());
      break;
    }
    case SharedMem::CONSTRAINT_LOG: {
      // Acquire query from shared memory
      ConstraintManager cm;
      std::vector<const Array *> arrays;
      auto query = deserializer.deserializeQuery(cm, arrays);
      auto res = coreSolver->getConstraintLog(query);

      serializer.serializeConstraintLogAnswer(res);
      free(res);
      break;
    }
    case SharedMem::COMPUTE_TRUTH: {
      // Acquire query from shared memory
      ConstraintManager cm;
      std::vector<const Array *> arrays;
      auto query = deserializer.deserializeQuery(cm, arrays);

      bool isValid;
      bool success = solver->impl->computeTruth(query, isValid);

      serializer.serializeComputeTruthAnswer(isValid);
      break;
    }
    case SharedMem::COMPUTE_VALUE: {
      // Acquire query from shared memory
      ConstraintManager cm;
      std::vector<const Array *> arrays;
      auto query = deserializer.deserializeQuery(cm, arrays);

      ref<Expr> result;
      bool success = solver->impl->computeValue(query, result);

      serializer.serializeComputeValueAnswer(result);
      break;
    }
    default:
      assert(0 && "Command unknown");
    }
    // Signal request producer that we are done
    request.signal(SharedMem::PRODUCER);
  }
  return 0;
}
