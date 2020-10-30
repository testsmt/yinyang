import unittest
import sys
import os
sys.path.append("../../")

from src.parsing.ast import * 
from src.parsing.parse import *
from src.generators.SemanticFusion.SemanticFusion import *
from src.generators.SemanticFusion.MetamorphicTuple import * 

class SemanticFusionTestCase(unittest.TestCase): 
    def test_sf_sat(self):
        fcts= """
        #begin
        (declare-const x Int)
        (declare-const y Int)
        (declare-const z Int)
        (declare-const c Int)
        (assert (= z (+ x c) y))
        (assert (= x (- (- z c) y)))
        (assert (= y (- (- z c) x)))
        #end
        """
        formula1="""
        (declare-const x Int)
        (assert (= x (- 1)))
        """
        formula2 = """
        (declare-const y Int)
        (declare-const v Bool)
        (assert (= v (not (= y (- 1)))))
        (assert (ite v false (= y (- 1))))
        (check-sat)
        """
        fn1, fn2, fn_fcts = "formula1.smt2","formula2.smt2","fcts.txt"
        with open(fn_fcts, "w") as f1:
            f1.write(fcts)
        with open(fn1, "w") as f1:
            f1.write(formula1)
        with open(fn2, "w") as f2:
            f2.write(formula2)
        sf_sat = SemanticFusion([fn1, fn2], "sat", "./config/fusion_functions.txt")
        sf_unsat = SemanticFusion([fn1, fn2], "unsat", "./config/fusion_functions.txt")
        sf_sat.generate()
        os.system("rm -rf "+fn1+ " "+ fn2+" "+fn_fcts)


if __name__ == '__main__':
    #SemanticFusionTestCase().test_sf_sat()
    unittest.main()

