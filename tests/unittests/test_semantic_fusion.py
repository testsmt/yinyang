import unittest
import os
import sys
sys.path.append("../../")

from src.parsing.ast import * 
from src.parsing.parse import *
from src.generators.SemanticFusion.SemanticFusion import *
from src.generators.SemanticFusion.VariableFusion import * 

class Mockargs:
    oracle = ""
    fusionfun = "."

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
        args = Mockargs()
        args.oracle = "sat"
        args.fusionfun = "./config/fusion_functions.txt"
        script1 = parse_file(fn1,silent=True)
        script2 = parse_file(fn2,silent=True)
        sf_sat = SemanticFusion(script1, script2, args)
        args.oracle = "unsat"

        script1 = parse_file(fn1,silent=True)
        script2 = parse_file(fn2,silent=True)
        sf_unsat = SemanticFusion(script1, script2, args)
        sf_sat.generate()
        os.system("rm -rf "+fn1+ " "+ fn2+" "+fn_fcts)


if __name__ == '__main__':
    #SemanticFusionTestCase().test_sf_sat()
    unittest.main()

