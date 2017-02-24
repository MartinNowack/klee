##===- unittests/Assignment/Makefile -----------------------*- Makefile -*-===##

LEVEL := ../..
include $(LEVEL)/Makefile.config

TESTNAME := Assignment
USEDLIBS := kleaverSolver.a kleaverExpr.a kleeSupport.a kleeBasic.a kleaverSolver.a
LINK_COMPONENTS := support

include $(LLVM_SRC_ROOT)/unittests/Makefile.unittest

CXXFLAGS += -DLLVM_29_UNITTEST
