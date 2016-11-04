//===-- InstructionInfoTable.cpp ------------------------------------------===//
//
//                     The KLEE Symbolic Virtual Machine
//
// This file is distributed under the University of Illinois Open Source
// License. See LICENSE.TXT for details.
//
//===----------------------------------------------------------------------===//

#include "klee/Internal/Module/InstructionInfoTable.h"
#include "klee/Config/Version.h"
#include "klee/Internal/Support/ErrorHandling.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(3, 3)
#include "llvm/IR/Function.h"
#include "llvm/IR/Instructions.h"
#include "llvm/IR/IntrinsicInst.h"
#include "llvm/IR/Module.h"
#else
#include "llvm/Function.h"
#include "llvm/Instructions.h"
#include "llvm/IntrinsicInst.h"
#include "llvm/Module.h"
#endif

# if LLVM_VERSION_CODE < LLVM_VERSION(3,5)
#include "llvm/Assembly/AssemblyAnnotationWriter.h"
#include "llvm/Support/InstIterator.h"
#include "llvm/Linker.h"
#else
#include "llvm/IR/AssemblyAnnotationWriter.h"
#include "llvm/IR/InstIterator.h"
#include "llvm/Linker/Linker.h"
#endif

#include "llvm/Support/FormattedStream.h"
#include "llvm/Support/raw_ostream.h"

#if LLVM_VERSION_CODE >= LLVM_VERSION(3,5)
#include "llvm/IR/DebugInfo.h"
#elif LLVM_VERSION_CODE >= LLVM_VERSION(3, 2)
#include "llvm/DebugInfo.h"
#include "llvm/Transforms/Utils/Local.h"
#else
#include "llvm/Analysis/DebugInfo.h"
#endif

#include "llvm/Analysis/ValueTracking.h"
#include "llvm/Support/ErrorHandling.h"

#include <map>
#include <string>

using namespace llvm;
using namespace klee;

class InstructionToLineAnnotator : public llvm::AssemblyAnnotationWriter {
public:
  void emitInstructionAnnot(const Instruction *i,
                            llvm::formatted_raw_ostream &os) {
    os << "%%%";
    os << (uintptr_t) i;
  }
};
        
static void buildInstructionToLineMap(Module *m,
                                      std::map<const Instruction*, unsigned> &out) {  
  InstructionToLineAnnotator a;
  std::string str;
  llvm::raw_string_ostream os(str);
  m->print(os, &a);
  os.flush();
  const char *s;

  unsigned line = 1;
  for (s=str.c_str(); *s; s++) {
    if (*s=='\n') {
      line++;
      if (s[1]=='%' && s[2]=='%' && s[3]=='%') {
        s += 4;
        char *end;
        unsigned long long value = strtoull(s, &end, 10);
        if (end!=s) {
          out.insert(std::make_pair((const Instruction*) value, line));
        }
        s = end;
      }
    }
  }
}

static std::string getDSPIPath(DILocation Loc) {
  std::string dir = Loc.getDirectory();
  std::string file = Loc.getFilename();
  if (dir.empty() || file[0] == '/') {
    return file;
  } else if (*dir.rbegin() == '/') {
    return dir + file;
  } else {
    return dir + "/" + file;
  }
}

static std::string concatLocation(const std::string &dir,
                                  const std::string &file) {
  if (dir.empty() || file[0] == '/') {
    return file;
  } else if (*dir.rbegin() == '/') {
    return dir + file;
  } else {
    return dir + "/" + file;
  }
}

bool InstructionInfoTable::getInstructionDebugInfo(llvm::Instruction *I,
                                                   const std::string *&File,
                                                   unsigned &Line,
                                                   unsigned &Column,
                                                   LLVMContext &context) {
#if LLVM_VERSION_CODE > LLVM_VERSION(2, 9)

  DbgDeclareInst *DDI = 0;
  if (isa<AllocaInst>(I)) {
    DDI = FindAllocaDbgDeclare(I);
  } else if (isa<StoreInst>(I) || isa<LoadInst>(I)) {
    // Check if the following instruction is a DbgDeclareIsnt
    BasicBlock::iterator it(I);
    ++it;
    DDI = dyn_cast<DbgDeclareInst>(&*it);
  }
  if (DDI) {
    // Get variable description meta data
    DIVariable var_node(DDI->getVariable());
    File = internString(var_node.getFile().getFilename());
    Line = var_node.getLineNumber();
    // Column information is not available, default it to 0
    Column = 0;
    return true;
  }

  const DebugLoc &loc = I->getDebugLoc();

  // Check if we know anything about this code location
  if (loc.isUnknown())
    return false;

  Line = loc.getLine();
  Column = loc.getCol();

  MDNode *scope = 0;
  MDNode *inlinedAt = 0;
  loc.getScopeAndInlinedAt(scope, inlinedAt, context);

  assert(scope && "Scope invalid");

  // Handle scope
  DILocation scopeLoc(scope);
  File = internString(getDSPIPath(scopeLoc));

  if (inlinedAt) {
    DILocation inlinedLoc(inlinedAt);
    File = internString(getDSPIPath(inlinedLoc));
  } else {

    DILocation Loc(loc.getAsMDNode(context));
    File = internString(getDSPIPath(Loc));
  }
  return true;
#else
  if (AllocaInst *ai = dyn_cast<AllocaInst>(I)) {
    Value *const V[] = {ai};
    if (MDNode *DebugNode = MDNode::getIfExists(context, V, 1)) {
      for (Value::use_iterator UI = DebugNode->use_begin(),
                               E = DebugNode->use_end();
           UI != E; ++UI) {
        if (DbgDeclareInst *DDI = dyn_cast<DbgDeclareInst>(*UI)) {
          // Get variable description meta data
          DIVariable var_node(DDI->getVariable());
          File = internString(
              concatLocation(var_node.getCompileUnit().getDirectory(),
                             var_node.getCompileUnit().getFilename()));
          Line = var_node.getLineNumber();
          // Column information is not available, default it to 0
          Column = 0;
          return true;
        }
      }
    }
  }

  const DebugLoc &loc = I->getDebugLoc();

  // Check if we know anything about this code location
  if (loc.isUnknown())
    return false;
  //  loc.dump(context);
  Line = loc.getLine();
  Column = loc.getCol();

  MDNode *scope = 0;
  MDNode *inlinedAt = 0;
  loc.getScopeAndInlinedAt(scope, inlinedAt, context);

  assert(scope && "Scope invalid");

  // Handle scope
  DILocation scopeLoc(scope);
  File = internString(getDSPIPath(scopeLoc));

  if (inlinedAt) {
    DILocation inlinedLoc(inlinedAt);
    File = internString(getDSPIPath(inlinedLoc));
  } else {

    DILocation Loc(loc.getAsMDNode(context));
    File = internString(getDSPIPath(Loc));
  }
  return true;
#endif
  return false;
}

InstructionInfoTable::InstructionInfoTable(Module *m)
    : dummyString(""), dummyInfo(0, dummyString, 0, 0, 0) {
  unsigned id = 0;
  std::map<const Instruction*, unsigned> lineTable;
  buildInstructionToLineMap(m, lineTable);

  llvm::DebugInfoFinder DbgFinder;
  DbgFinder.processModule(*m);

  // process debug information of functions
  for (DebugInfoFinder::iterator fIt = DbgFinder.subprogram_begin(),
                                 fItE = DbgFinder.subprogram_end();
       fIt != fItE; ++fIt) {
    DISubprogram SubP(*fIt);
    assert(SubP.Verify());
    if (SubP.getFunction() == 0)
      continue;

    // skip if information already acquired.
    // e.g. due to multiple includes of the same files
    if (functionInfos.count(SubP.getFunction()))
      continue;

    unsigned assemblyLine = 0;
    Function *f = SubP.getFunction();
    if (!f->isDeclaration()) {
      assemblyLine = lineTable[f->getEntryBlock().begin()];
    }
    functionInfos.insert(std::make_pair(
        SubP.getFunction(),
        InstructionInfo(0, *internString(concatLocation(SubP.getDirectory(),
                                                        SubP.getFilename())),
                        SubP.getLineNumber(), 0, assemblyLine)));
    }

    for (Module::iterator fnIt = m->begin(), fn_ie = m->end(); fnIt != fn_ie;
         ++fnIt) {

      const std::string *file = &dummyString;
      unsigned line = 0;
      unsigned column = 0;
      for (inst_iterator it = inst_begin(fnIt), ie = inst_end(fnIt); it != ie;
           ++it) {
        Instruction *instr = &*it;
        unsigned assemblyLine = lineTable[instr];

        // Update our source level debug information.
        if (!getInstructionDebugInfo(instr, file, line, column,
                                     m->getContext())) {
          file = &dummyString;
          line = 0;
          column = 0;
        }

        infos.insert(std::make_pair(
            instr, InstructionInfo(id++, *file, line, column, assemblyLine)));
      }
  }
}

InstructionInfoTable::~InstructionInfoTable() {
  for (std::set<const std::string *, ltstr>::iterator
         it = internedStrings.begin(), ie = internedStrings.end();
       it != ie; ++it)
    delete *it;
}

const std::string *InstructionInfoTable::internString(std::string s) {
  std::set<const std::string *, ltstr>::iterator it = internedStrings.find(&s);
  if (it==internedStrings.end()) {
    std::string *interned = new std::string(s);
    internedStrings.insert(interned);
    return interned;
  } else {
    return *it;
  }
}

unsigned InstructionInfoTable::getMaxID() const {
  return infos.size();
}

const InstructionInfo &
InstructionInfoTable::getInfo(const Instruction *inst) const {
  unordered_map<const llvm::Instruction *, InstructionInfo>::const_iterator it =
      infos.find(inst);
  if (it == infos.end())
    klee_error("invalid instruction, not present in initial module!");
  return it->second;
}

const InstructionInfo &
InstructionInfoTable::getFunctionInfo(const Function *f) const {
  if (f->isDeclaration()) {
    // FIXME: We should probably eliminate this dummyInfo object, and instead
    // allocate a per-function object to track the stats for that function
    // (otherwise, anyone actually trying to use those stats is getting ones
    // shared across all functions). I'd like to see if this matters in practice
    // and construct a test case for it if it does, though.
    return dummyInfo;
  }

  // use debug information of the function if available
  // otherwise return debug information of the first instruction of the function
  const InstructionInfo &firstInst = getInfo(f->begin()->begin());
  unordered_map<const llvm::Function *, InstructionInfo>::const_iterator it =
      functionInfos.find(f);
  if (it == functionInfos.end())
    return firstInst;
  return it->second;
}
