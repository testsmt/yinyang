import unittest
import sys
sys.path.append("../../")

from src.parsing.ast import *
from src.parsing.parse import *
from src.parsing.typechecker import *
from src.parsing.types import *



class TypecheckerTestCase(unittest.TestCase):
    def test_core_theory(self):
        formula_str="""
                (declare-const y Int)
                (declare-const v Bool)
                (assert (= v (not (= y (- 1)))))
                (check-sat)
        """
        equal = parse_str(formula_str).commands[2].term
        self.assertEqual(typecheck_expr(equal), BOOLEAN_TYPE)
        v = equal.subterms[0]
        self.assertEqual(typecheck_expr(v),BOOLEAN_TYPE)
        not_op = equal.subterms[1]
        self.assertEqual(typecheck_expr(not_op), BOOLEAN_TYPE)
        y = equal.subterms[1].subterms[0].subterms[0]
        self.assertEqual(typecheck_expr(y), INTEGER_TYPE)
        minusone= equal.subterms[1].subterms[0].subterms[1]
        self.assertEqual(typecheck_expr(minusone), INTEGER_TYPE)

        formula_str="""
                (declare-const y Int)
                (declare-const v Bool)
                (assert (ite v false (= y (- 1))))
                (check-sat)
        """
        ite = parse_str(formula_str).commands[2].term
        self.assertEqual(typecheck_expr(ite), BOOLEAN_TYPE)

        # Dominik: looks wrong to me 
        # formula_str="""
                # (declare-const y Int)
                # (declare-const v Bool)
                # (assert (and (ite v false (= y (- 1))) (= v (not (= y (- 1))))))
                # (check-sat)
        # """
        # and_expr = parse_str(formula_str)
        # self.assertEqual(typecheck_expr(and_expr), BOOLEAN_TYPE)
    
    # TODO: expect type error here
    def test_error(self):
        formula_str="""
                (declare-const y Int)
                (declare-const v Bool)
                (assert (= v (not (= v (- 1)))))
                (check-sat)
        """
        equal = parse_str(formula_str).commands[2].term
        # print(typecheck_expr(equal))

    def test_typecheck_nary_int_ret(self):
        formula_str="""
                (declare-const v Int)
                (declare-const w Int)
                (assert (= v (+ v v w)))
                (check-sat)
        """
        nary_plus = parse_str(formula_str).commands[2].term.subterms[1]
        self.assertEqual(typecheck_expr(nary_plus), INTEGER_TYPE)
    
    def test_typecheck_comp_ops(self):
        formula_str="""
                (declare-const v Int)
                (declare-const w Int)
                (assert (> v (+ v v w)))
                (check-sat)
        """
        greater = parse_str(formula_str).commands[2].term
        self.assertEqual(typecheck_expr(greater), BOOLEAN_TYPE)


if __name__ == '__main__':
    TypecheckerTestCase.test_typechecker()
    unittest.main()

