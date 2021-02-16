"""
Illustrates parser and typechecker on simple SMT formula/script.  
"""
import time
import sys  
from src.parsing.ast import *  
from src.parsing.parse import *  
from src.parsing.typechecker import *  
from src.parsing.typechecker_recur import *

formula1=\
"""
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x y))
"""

formula1, _ = parse_str(formula1,silent=False)

formula2=\
"""
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= y y))
"""
formula2, _ = parse_str(formula1,silent=False)

# Emulation of issue 



