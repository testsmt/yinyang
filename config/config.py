# Solver configurations list to be used for fuzzing.
solvers = ["z3release model_validate=true",                                               
           "z3release model_validate=true smt.arith.solver=2",                            
           "z3release model_validate=true smt.arith.solver=3",                            
           "z3release model_validate=true smt.arith.solver=6",                            
           "z3release model_validate=true rewriter.flat=false",                           
           "cvc4 --check-models --produce-models --incremental --strings-exp -q",         
           "cvc4 --no-strings-lazy-pp --check-models --produce-models --incremental --strings-exp -q",
           "cvc4 --strings-lazy-pp --check-models --produce-models --incremental --strings-exp -q",
           "cvc4 --check-unsat-cores --check-models --produce-models --incremental --strings-exp -q",
           "cvc4 --check-models --produce-models --incremental --strings-exp --ext-rewrite-quant -q"
]

# Crash list: crash messages emitted by solvers to consider as bugs.
crash_list = [
    "Exception",
    "lang.AssertionError",
    "lang.Error",
    "runtime error",
    "LEAKED",
    "Leaked",
    "Segmentation fault",
    "segmentation fault",
    "segfault",
    "ASSERTION",
    "Assertion",
    "Fatal failure",
    "Internal error detected",
    "an invalid model was generated",
    "Failed to verify",
    "failed to verify",
    "ERROR: AddressSanitizer:",
    "invalid expression",
    "Aborted"
]

# Duplicate list: crash messages emitted by solvers to be considered duplicates,
# i.e. will be ignored during fuzzing.
duplicate_list = [

]

# Ignore list: error messages emitted by solvers to be ignored.
ignore_list = [
   "(error ",
    "unsupport",
    "unexpected char",
    "failed to open file",
    "Expected result sat but got unsat",
    "Expected result unsat but got sat",
    "Parse Error",
    "Cannot get model",
    "Symbol 'str.to-re' not declared as a variable",
    "Symbol 'str.to.re' not declared as a variable",
    "Unimplemented code encountered",
]
