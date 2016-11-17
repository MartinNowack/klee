//===-- ExecutorValidator.cpp -----------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//
#include "Executor.h"

#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Internal/Support/ErrorHandling.h"

#include "llvm/Support/CommandLine.h"
#include "llvm/Support/raw_ostream.h"

#include <fstream>

namespace klee {

void Executor::initializeValidationFile(std::string &name) {
  if (name.empty())
    return;

  validationFile = new std::ifstream(name.c_str(), std::ios::in);
  if (!validationFile->good())
    klee_error("Could not open validation file %s", name.c_str());
}

void Executor::checkInstructions(ExecutionState &state) {
  if (!validationFile)
    return;
  // get file line
  std::string line;
  (*validationFile) >> line;

  llvm::StringRef l(line);
  std::pair<llvm::StringRef, llvm::StringRef> res = l.split(":");

  unsigned instruction_id;
  bool c = res.first.getAsInteger(0, instruction_id);
  // XXX something is wrong with the integer parsing
  //    if (!c)
  //      klee_warning("Parsing error of validation file. Failed: '%s', %u",
  //      res.first.str().c_str(), instruction_id);

  uint64_t state_uid;
  c = res.second.getAsInteger(0, state_uid);
  //    if (!c)
  //      klee_warning("Parsing error of validation file. Failed: '%s', %lu",
  //      res.second.str().c_str(), state_uid);

  // compare with current state
  if (state.pc->info->id != instruction_id || state.uid != state_uid) {
    klee_error("Execution diverged. Expected state %lu and found %lu. "
               "Expected instruction id %u and found %u",
               state_uid, state.uid, instruction_id, state.pc->info->id);
  }
}
}
