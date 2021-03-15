from src.parsing.parse import *  
#
# Dominik: Illustrates usage of parent pointer.    
#         @Jiwon: this and the whole algorithm (described on Slack) will need to 
#          be unit tested with interesting formulas, lets, quantifiers.  
#
formula1=\
"""
(declare-fun x () Int)
(declare-fun y () Int)
(assert (= x y))
"""
formula1, _ = parse_str(formula1,silent=False)
equals = formula1.commands[2].term
assert(equals.parent ==  None)
x = formula1.commands[2].term.subterms[0]
y = formula1.commands[2].term.subterms[1]
assert(x.parent == y.parent == equals) 
