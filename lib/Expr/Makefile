#===-- lib/Expr/Makefile -----------------------------------*- Makefile -*--===#
#
#                     The KLEE Symbolic Virtual Machine
#
# This file is distributed under the University of Illinois Open Source
# License. See LICENSE.TXT for details.
#
#===------------------------------------------------------------------------===#

LEVEL=../..

LIBRARYNAME=kleaverExpr
DONT_BUILD_RELINKED=1
BUILD_ARCHIVE=1
NO_INSTALL=1

all-local:: proto-rebuild

include $(LEVEL)/Makefile.common

proto-rebuild:
	capnp compile -oc++ $(PROJ_SRC_ROOT)/lib/Expr/Expressions.capnp