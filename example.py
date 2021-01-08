"""
Illustrates parser and typechecker on simple SMT formula/script.  
"""
import time
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

start_time = time.time()
av_expr, expr_type = typecheck_recur_list(first_assert,ctxt)
print("execution time for list: {}".format(time.time()-start_time))
print("number of available expressions: {}".format(len(av_expr)))
str_expr = []
for i in range(len(av_expr)):
    str_expr.append((str(av_expr[i]),expr_type[i]))
print(str_expr)
