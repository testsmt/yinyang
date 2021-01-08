import unittest
import sys
sys.path.append("../../")
import os

from src.parsing.parse import *
from src.parsing.typechecker import Context
from src.generators.TypeAwareOpMutation import TypeAwareOpMutation
from src.generators.TypeMutation import TypeMutation

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
        (check-sat)
        """
        with open(formulafile,"w") as f: 
            f.write(formula)
        script, glob = parse_str(formula)
        ctxt = Context(glob,{})
        args = Mockargs()
        print(formulafile)
        args.name = formulafile.strip(".smt2")
        gen = TypeMutation([formulafile],args,ctxt)
        gen.generate()
        os.system("rm -rf "+formulafile)


if __name__ == '__main__':
    #TypeAwareOpMutationTestCase.test_ta()
    unittest.main()

