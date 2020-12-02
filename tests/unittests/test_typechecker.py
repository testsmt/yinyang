import unittest
import sys
sys.path.append("../../")

from src.parsing.ast import *
from src.parsing.parse import *
from src.parsing.typechecker import *


class TypecheckerTestCase(unittest.TestCase):
    def test_typechecker(self):
        formula1_str="""
                (declare-const y Int)
                (declare-const v Bool)
                (assert (= v (not (= y (- 1)))))
                (assert (ite v false (= y (- 1))))
                (check-sat)
        """
        not_op = parse_str(formula1_str).commands[2].term.subterms[1]
        # not_op = parse_str(formula1_str).commands[3].term.subterms[0]
        print(typecheck_expr(not_op))
        # self.assertEquals()

if __name__ == '__main__':
    #SemanticFusionTestCase().test_sf_sat()
    TypecheckerTestCase.test_typechecker()
    unittest.main()

