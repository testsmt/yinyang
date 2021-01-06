"""
Illustrates parser and typechecker on simple SMT formula/script.  
"""
import sys  
from src.parsing.ast import *  
from src.parsing.parse import *  
from src.parsing.typechecker import *  
from src.parsing.typechecker_recur import *

formula=\
"""
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (> (* (+ 3 x) (- y 2)) (/ 5 z)))
(check-sat)
"""

# 1. Parse formula; generates AST for SMT commands carrying expressions, e.g., 
# asserts    
formula, glob = parse_str(formula,silent=False)
print(formula)

# 2. Typecheck the terms inside the first assert.  
ctxt=Context(glob,{}) # carries locals and globals see src/ast/typechecker.py 
first_assert=formula.commands[3]
av_expr, expr_type = typecheck_recur(first_assert,ctxt)
print("number of available expressions: {}".format(len(av_expr)))
print("length of dictionary: {}".format(len(expr_type)))
print(expr_type)
