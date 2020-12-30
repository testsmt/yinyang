"""
Illustrates parser and typechecker on simple SMT formula/script.  
"""
import sys  
from src.parsing.ast import *  
from src.parsing.parse import *  
from src.parsing.typechecker import *  

formula=\
"""
(declare-fun x () Int)
(declare-fun w () Bool)
(assert (= 1 1))
(assert w)
(check-sat)
"""

# 1. Parse formula; generates AST for SMT commands carrying expressions, e.g., 
# asserts    
formula, _ = parse_str(formula,silent=False)
print(formula)

# 2. Typecheck the terms inside the first assert.  
ctxt=Context({},{}) # carries locals and globals see src/ast/typechecker.py 
# 
first_assert=formula.commands[2]
t = typecheck_expr(first_assert.term,ctxt)
print(t)
