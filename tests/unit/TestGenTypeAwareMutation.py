import unittest
import sys
sys.path.append("../../")
import os

from src.parsing.Parse import *
from src.parsing.Typechecker import Context, typecheck
from src.mutators.GenTypeAwareMutation.GenTypeAwareMutation import *
from src.mutators.GenTypeAwareMutation.util import *


class Mockargs:
    modulo = 3
    config = "config/generalization.txt"

class GenTypeAwareMutationTestCase(unittest.TestCase):
    def test_ta(self):
        formulafile="formula.smt2"
        formula = """
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (assert (> (* (+ 3 x) (- y 2)) (div 5 z)))
        (assert (= (+ 7 y) x))
        (assert (< 6 (div (+ 4 x) z)))
        (check-sat)
        """
        with open(formulafile,"w") as f:
            f.write(formula)
        script, glob = parse_str(formula)
        typecheck(script, glob)
        args = Mockargs()
        args.name = formulafile.strip(".smt2")
        script, glob = parse_file(formulafile,silent=True)
        typecheck(script, glob)
        self.av_expr, self.expr_type = get_all_subterms(script)
        unique_expr = get_unique_subterms(script)
        gen = GenTypeAwareMutation(script,args,unique_expr)
        gen.generate()
        os.system("rm "+formulafile)


if __name__ == '__main__':
    unittest.main()

