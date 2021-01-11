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

class TypeAwareOpMutationTestCase(unittest.TestCase):

    def test_ta(self):
        formulafile="formula.smt2"
        formula = """
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (assert (> (* (+ 3 x) (- y 2)) (/ 5 z)))
        (assert (= (+ 7 y) x))
        (assert (distinct z x))
        (assert (= 1 1.0))
        (assert true)
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


if __name__ == '__main__':
    #TypeAwareOpMutationTestCase.test_ta()
    unittest.main()

