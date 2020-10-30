solvers = [
    "cvc4 --strings-exp --incremental --produce-models --check-unsat-cores --check-models --quiet",
    "cvc4 --strings-exp --sygus-inference --produce-models --check-unsat-cores --check-models --quiet",
    "z3release model_validate=true",
    "z3release smt.ematching=false rewriter.flat=false smt.threads=3 smt.arith.solver=2 model_validate=true",
    "z3release smt.ematching=false rewriter.flat=false smt.threads=3 model_validate=true"
]

crash_msgs = [
    "LEAKED",
    "Leaked",
    "Segmentation fault",
    "segmentation fault",
    "segfault",
    "ASSERTION VIOLATION",
    "Assertion failure",
    "Fatal failure",
    "Internal error detected",
    "an invalid model was generated",
    "Failed to verify",
    "failed to verify",
    "ERROR: AddressSanitizer:",
    "invalid expression"
]

ignore_msgs = [
    "(error",
    "Expected result sat but got unsat",
    "Expected result unsat but got sat",
    "Parse Error",
    "Cannot get model",
    "Symbol 'str.to-re' not declared as a variable",
    "Symbol 'str.to.re' not declared as a variable",
    "Unimplemented code encountered",
    '(error "Error in option parsing: sygus inference not supported with incremental solving")'
]
