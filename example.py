"""
Illustrates parser and typechecker on simple SMT formula/script.  
"""
import time
import sys  
from src.parsing.ast import *  
from src.parsing.parse import *  
from src.parsing.typechecker import *  

formula1=\
"""
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x y))
"""
formula1, _ = parse_str(formula1,silent=False)
