import unittest
import sys
sys.path.append("../../")
import os 

from src.parsing.parse import *
from src.generators.TypeAwareOpMutation import TypeAwareOpMutation

class TypeAwareOpMutationTestCase(unittest.TestCase):
    def test_ta(self):
        configfile="operators.txt"
        formulafile="formula.smt2"
        ops= """
        =,distinct
        exists,forall
        and,or,=>
        <=, >=,<,>
        +,-,*,/ :arity 2+
        div,mod
        """
        with open(configfile,"w") as f:
            f.write(ops)

        formula = """
        (declare-const x Int)                                                      
        (declare-const y Int)                                                     
        (declare-const w Bool)
        (assert (= x (- x)))                                                       
        (assert (distinct w (= x (- y))))                                          
        (assert w)                                                                 
        (check-sat) 
        """
        with open(formulafile,"w") as f: 
            f.write(formula)
        script = parse_str(formula)
        gen = TypeAwareOpMutation([formulafile],config_file=configfile)
        gen.generate()
        os.system("rm -rf "+configfile+ " "+ formulafile)

        

if __name__ == '__main__':
    TypeAwareOpMutationTestCase.test_ta()
    #unittest.main()

