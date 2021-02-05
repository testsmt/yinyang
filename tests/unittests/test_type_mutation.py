import unittest
import sys
sys.path.append("../../")
import os

from src.parsing.parse import *
from src.parsing.typechecker import Context
from src.generators.TypeAwareOpMutation import TypeAwareOpMutation
from src.generators.TypeMutation import *

class Mockargs:
    name = ""

N = 200

class TypeAwareMutationTestCase(unittest.TestCase):

    def test_ta(self):
        formulafile="formula.smt2"
        formula = """
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (assert (> (* (+ 3 x) (- y 2)) (/ 5 z)))
        (assert (= (+ 7 y) x))
        (assert (< 6 (/ (+ 4 x) z)))
        (check-sat)
        """
        with open(formulafile,"w") as f: 
            f.write(formula)
        script, glob = parse_str(formula)
        ctxt = Context(glob,{})
        args = Mockargs()
        args.name = formulafile.strip(".smt2")
        script, _ = parse_file(formulafile,silent=True)
        gen = TypeMutation(script,args)
        gen.generate()
        os.system("rm "+formulafile)

    def test_mutation(self):
        formulafile="formula.smt2"
        formula = """
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun a () Real)
        (declare-fun b () Real)
        (assert (> (/ x 3) (+ a b)))
        (assert (= (+ 4 y) x))
        (assert (distinct a b))
        (check-sat)
        """
        possible_outcome = ["(assert (distinct (/ x 3) b))",
                            "(assert (= x (+ 4 y)))",
                            "(assert (> a (+ a b)))",
                            "(assert (distinct a (+ a b)))",
                            "(assert (> (/ (+ 4 y) 3) (+ a b)))"                           
                            ]
        with open(formulafile,"w") as f: 
            f.write(formula)
        script, glob = parse_str(formula)
        ctxt = Context(glob,{})
        args = Mockargs()
        print(formulafile)
        args.name = formulafile.strip(".smt2")
        for i in range(N):
            script, _ = parse_file(formulafile,silent=True)
            gen = TypeMutation(script,args)
            gen.generate()
            for cmd in gen.formula.assert_cmd:
                if str(cmd) in possible_outcome:
                    possible_outcome.remove(str(cmd))
            if not possible_outcome:
                os.system("rm "+formulafile)
                return True
        os.system("rm "+formulafile)
        return False


if __name__ == '__main__':
    unittest.main()

