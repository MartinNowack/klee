##===- performancetests/Expr/Makefile -----------------------------*- Makefile -*-===##

LEVEL := ../..

TESTNAME := Expr
USEDLIBS :=kleaverSolver.a kleaverExpr.a kleeBasic.a kleeSupport.a
LINK_COMPONENTS := support

include $(LEVEL)/Makefile.common

PerfTest = $(BuildMode)/$(TESTNAME)Tests
TESTLIBS = -lbenchmark -pthread -lrt

$(PerfTest):  $(ObjectsO) $(ProjLibsPaths) $(LLVMLibsPaths)
	$(Echo) Linking $(BuildMode) Performance test $(TESTNAME) $(StripWarnMsg)
	$(Verb) $(Link) -o $@ $(TOOLLINKOPTS) $(ObjectsO) $(ProjLibsOptions) \
	$(TESTLIBS) $(LLVMLibsOptions) $(ExtraLibs) $(TOOLLINKOPTSB) $(LIBS)
	$(Echo) ======= Finished Linking $(BuildMode) Performance test $(TESTNAME) \
	$(StripWarnMsg)

all:: $(PerfTest)
	./$(PerfTest)
LIBS += $(STP_LDFLAGS)
LIBS += $(CAPNPROTO_LDFLAGS)