import unittest
import sys
sys.path.append("../../")

from src.parsing.ast import *
from src.parsing.parse import *
from src.parsing.typechecker import *
from src.parsing.types import *


class TypecheckerTestCase(unittest.TestCase):
    def test_core_theory(self):
        formula_str=\
"""
(declare-const y Int)
(declare-const v Bool)
(assert (= v (not (= y (- 1)))))
(check-sat)
"""
        formula,_ = parse_str(formula_str)
        equals=formula.commands[2].term
        self.assertequals(typecheck_expr(equal), BOOLEAN_TYPE)
        v = equals.subterms[0]
        self.assertequals(typecheck_expr(v),BOOLEAN_TYPE)
        not_op = equals.subterms[1]
        self.assertequals(typecheck_expr(not_op), BOOLEAN_TYPE)
        y = equals.subterms[1].subterms[0].subterms[0]
        self.assertequals(typecheck_expr(y), INTEGER_TYPE)
        minusone= equals.subterms[1].subterms[0].subterms[1]
        self.assertequals(typecheck_expr(minusone), INTEGER_TYPE)

        formula_str=\
"""
(declare-const y Int)
(declare-const v Bool)
(assert (ite v false (= y (- 1))))
(check-sat)
"""
        ite, _ = parse_str(formula_str).commands[2].term
        self.assertEqual(typecheck_expr(ite), BOOLEAN_TYPE)


    def test_error(self):
        formula_str=\
"""
(declare-const y Int)
(declare-const v Bool)
(assert (= v (not (= v (- 1)))))
(check-sat)
"""
        formula, _ = parse_str(formula_str)
        equals=formula.commands[2].term
        no_excpt=True
        try:
            typecheck_expr(equal)
        except:
            no_except=False
        self.assertFalse(no_except)


    def test_typecheck_nary_int_ret(self):
        formula_str=\
"""
(declare-const v Int)
(declare-const w Int)
(assert (= v (+ v v w)))
(check-sat)
"""
        formula, _ = parse_str(formula_str)
        nary_plus = formula.commands[2].term.subterms[1]
        self.assertEqual(typecheck_expr(nary_plus), INTEGER_TYPE)

    def test_typecheck_comp_ops(self):
        formula_str=\
"""
(declare-const v Int)
(declare-const w Int)
(assert (> v (+ v v w)))
(check-sat)
"""
        greater, _ = parse_str(formula_str).commands[2].term
        self.assertEqual(typecheck_expr(greater), BOOLEAN_TYPE)

    def test_typecheck_string_ops(self):
        formula_str=\
"""
(assert (distinct (str.replace_all "B" "A" "") "B"))
(check-sat)
"""
        formula, _ = parse_str(formula_str)
        distinct = formula.commands[0].term
        self.assertEqual(typecheck_expr(distinct), BOOLEAN_TYPE)
        str_repl=distinct.subterms[0]
        self.assertEqual(typecheck_expr(str_repl), STRING_TYPE)
        formula_str=\
"""
(declare-fun a () String)
(assert (str.contains (str.substr a 0 (- (str.len a) 1)) "A"))
(assert (= (ite (= (str.at a 0) "B") 1 0) (ite (= (str.at a 0) "A") 1 0) 0))
(assert (= (str.at a (- (str.len a) 1)) "B"))
(check-sat)
"""
        formula = parse_str(formula_str)
        for i in range(1, 4):
            typecheck_expr(formula.commands[i].term)

    def test_let_expression(self):
        formula_str=\
"""
(declare-sort S1 0)
(declare-fun f1 () S1)
(declare-fun f2 () S1)
(declare-fun f3 () Int)
(assert (not (= f1 f2)))
(assert (let ((?v_0 (+ (* 4 f3) 1))) (let ((?v_1 (* ?v_0 (- ?v_0 1)))) (not (=> (< ?v_1 (+ (- ?v_1 ?v_0) 2)) (< ?v_0 2))))))
(check-sat)
(exit)
"""
#TODO:

if __name__ == '__main__':
    TypecheckerTestCase.test_typechecker()
    unittest.main()
