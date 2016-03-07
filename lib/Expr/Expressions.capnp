###
#
# Serialization Protocoll for Expressions and Queries
#

@0x9c97b87345bd8998;
using Cxx = import "/capnp/c++.capnp";
$Cxx.namespace("klee::serial");

struct Expr {
  union {
    constantExpr :group {
        value @0 : UInt64;
        width @1 : UInt32;
    }
    largeConstantExpr : group {
        value @34 : List(UInt64);
        width @35 : UInt32;
    }
    readExpr :group {
        indexExpr @2 : UInt32;
        arrayIndex @3 : UInt32;
        updatesIndex @4 : UInt32;
    }
    selectExpr :group {
        kids @28 : List(UInt32);
    }
    concatExpr :group {
        kids @29 : List(UInt32);
    }
    extractExpr :group {
        kid @30: UInt32;
        offset @31: UInt32;
        width @32: UInt32;
    }
    
    zExtExpr :group {
        kid @12 : UInt32;
        width @14 : UInt32;
    }
    sExtExpr :group {
        kid @13 : UInt32;
        width @15 : UInt32;
    }
    addExpr :group {
        kids @5 : List(UInt32);
    }
    subExpr :group {
        kids @6 : List(UInt32);
    }
    mulExpr :group {
        kids @7 : List(UInt32);
    }
    uDivExpr :group {
        kids @8 : List(UInt32);
    }
    sDivExpr :group {
        kids @9 : List(UInt32);
    }
    uRemExpr :group {
        kids @10 : List(UInt32);
    }
    sRemExpr :group {
        kids @11 : List(UInt32);
    }
    notExpr : group {
        kids @16 : List(UInt32);
    }
    andExpr : group {
        kids @17 : List(UInt32);
    }
    orExpr : group {
        kids @18 : List(UInt32);
    }
   	xorExpr : group {
        kids @19 : List(UInt32);
    }
    shlExpr : group {
        kids @20 : List(UInt32);
    }
    lShrExpr : group {
        kids @21 : List(UInt32);
    }
    aShrExpr : group {
        kids @22 : List(UInt32);
    }
    eqExpr : group {
        kids @23 : List(UInt32);
    }
    ultExpr : group {
        kids @24 : List(UInt32);
    }
    uleExpr : group {
        kids @25 : List(UInt32);
    }
    sltExpr : group {
        kids @26 : List(UInt32);
    }
    sleExpr : group {
        kids @27 : List(UInt32);
    }
    notOptimizedExpr : group {
        kids @33 : List(UInt32);
    }
  }
}

struct UpdateNode {
  index @0 : UInt32;
  value @1 : UInt32;
  next @2: UInt32;
  size @3: UInt32;
  hashValue @4: UInt32;
}

# Pointer to update nodes
struct UpdateNodeBox {
  ptr @0: UpdateNode;
}

struct Array {
  name @0 : Text;
  size @1 : UInt64;
  domain @2 : UInt32;
  range @3 : UInt32;

  constantValue @4: List(UInt32);
}

struct ExprBox {
  ptr @0: Expr;
}

# Contains single expression and all referenced arrays
struct ExpressionContainer {
    exprIdx @0 :UInt32;
    arrays @1 :List(Array);
    updates @2 :List(UpdateNodeBox);
    expressions @3: List(ExprBox);
    success @4 : Bool;
}

# Contains whole Query
struct QueryContainer {
  constraints @0 :List(UInt32);
  query @1 :UInt32;

  arrays @2 :List(Array);
  updates @4 :List(UpdateNodeBox);

  requestedArrayIndex @3 : UInt64;
  
  expressions @5: List(ExprBox);
}

# Contains query answer
struct QueryResponse {
  success @0 : Bool;
  concreteValues @1 : List(Data);
  solverRunStatus @2 : UInt8;
  hasSolution @3 : Bool;
}

struct ConstraintLogResponse {
  response @0 : Text;
  success @1 : Bool;
}

struct ComputeTruthResponse {
  isValid @0 : Bool;
  success @1 : Bool;
}

# We currently use "ExpressionContainer"
# struct ComputeValueResponse {
#  result @0 : Expr;
#  success @1 : Bool;
#}
