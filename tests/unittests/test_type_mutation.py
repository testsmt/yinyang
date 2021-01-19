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

N = 5000
m = 50

class TypeAwareOpMutationTestCase(unittest.TestCase):

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
        print(formulafile)
        args.name = formulafile.strip(".smt2")
        gen = TypeMutation([formulafile],args)
        gen.generate()
        os.system("rm "+formulafile)

    def test_mutation(self):
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
        possible_outcome = ["(assert (= y x))",
                            "(assert (= x y))",
                            "(assert (< (+ 3 y) (/ (+ 4 x) z)))",
                            "(assert (= (- x y) 6))",
                            "(assert (> z (/ y x))"                            
                            ]
        with open(formulafile,"w") as f: 
            f.write(formula)
        script, glob = parse_str(formula)
        ctxt = Context(glob,{})
        args = Mockargs()
        print(formulafile)
        args.name = formulafile.strip(".smt2")
        gen = TypeMutation([formulafile],args)
        for i in range(N):
            if i % m == 0:
                gen = TypeMutation([formulafile],args)
            for cmd in gen.formula.assert_cmd:
                if str(cmd) in possible_outcome:
                    possible_outcome.remove(str(cmd))
            if not possible_outcome:
                return True
        return False



if __name__ == '__main__':
    #TypeAwareOpMutationTestCase.test_ta()
    unittest.main()

