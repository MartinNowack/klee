//===-- InstructionInfoTable.h ----------------------------------*- C++ -*-===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#ifndef KLEE_LIB_INSTRUCTIONINFOTABLE_H
#define KLEE_LIB_INSTRUCTIONINFOTABLE_H

#include <map>
#include <string>
#include <set>

#include <ciso646>
#ifdef _LIBCPP_VERSION
#include <unordered_map>
#define unordered_map std::unordered_map
#else
#include <tr1/unordered_map>
#define unordered_map std::tr1::unordered_map
#endif

namespace llvm {
  class Function;
  class Instruction;
  class Module;
  class LLVMContext;
}

namespace klee {

  /* Stores debug information for a KInstruction */
  struct InstructionInfo {
    unsigned id;
    const std::string &file;
    unsigned line;
    unsigned column;
    unsigned assemblyLine;

  public:
    InstructionInfo(unsigned _id, const std::string &_file, unsigned _line,
                    unsigned _column, unsigned _assemblyLine)
        : id(_id), file(_file), line(_line), column(_column),
          assemblyLine(_assemblyLine) {}
  };

  class InstructionInfoTable {
    struct ltstr { 
      bool operator()(const std::string *a, const std::string *b) const {
        return *a<*b;
      }
    };

    std::string dummyString;
    InstructionInfo dummyInfo;
    unordered_map<const llvm::Instruction *, InstructionInfo> infos;
    unordered_map<const llvm::Function *, InstructionInfo> functionInfos;
    std::set<const std::string *, ltstr> internedStrings;

  private:
    const std::string *internString(std::string s);
    bool getInstructionDebugInfo(llvm::Instruction *I, const std::string *&File,
                                 unsigned &Line, unsigned &Column,
                                 llvm::LLVMContext &context);

  public:
    InstructionInfoTable(llvm::Module *m);
    ~InstructionInfoTable();

    unsigned getMaxID() const;
    const InstructionInfo &getInfo(const llvm::Instruction*) const;
    const InstructionInfo &getFunctionInfo(const llvm::Function*) const;
  };

}

#endif
