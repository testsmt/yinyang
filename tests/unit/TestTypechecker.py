# MIT License
#
# Copyright (c) [2020 - 2021] The yinyang authors
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

import unittest
import sys
import pathlib

sys.path.append("../../")

from src.parsing.Ast import (
    Assert,
)
from src.parsing.Parse import (
    parse_str, parse_file
)

from src.parsing.Types import (
    UNKNOWN,
    BOOLEAN_TYPE,
    INTEGER_TYPE,
    STRING_TYPE,
)

from src.parsing.Typechecker import Context, typecheck_expr, typecheck


def check_type(expr):
    """
    recursive traversal of expressions to check whether none of them has
    unknown type.
    """
    if expr.type == UNKNOWN:
        raise Exception(expr.__str__() + " has unknown type")

    if expr.var_binders:
        for i, _ in enumerate(expr.var_binders):
            check_type(expr.let_terms[i])
        for e in expr.subterms:
            check_type(e)
    else:
        if expr.subterms:
            for e in expr.subterms:
                check_type(e)


def oracle(formula):
    for cmd in formula.commands:
        if isinstance(cmd, Assert):
            check_type(cmd.term)
    return True


class TypecheckerTestCase(unittest.TestCase):
    def test_core_theory(self):
        formula_str = """
(declare-const y Int)
(declare-const v Bool)
(assert (= v (not (= y (- 1)))))
(check-sat)
"""
        formula, globals = parse_str(formula_str)
        ctxt = Context(globals, {})
        equals = formula.commands[2].term
        self.assertEqual(typecheck_expr(equals, ctxt), BOOLEAN_TYPE)
        v = equals.subterms[0]
        self.assertEqual(typecheck_expr(v, ctxt), BOOLEAN_TYPE)
        not_op = equals.subterms[1]
        self.assertEqual(typecheck_expr(not_op, ctxt), BOOLEAN_TYPE)
        y = equals.subterms[1].subterms[0].subterms[0]
        self.assertEqual(typecheck_expr(y, ctxt), INTEGER_TYPE)
        minusone = equals.subterms[1].subterms[0].subterms[1]
        self.assertEqual(typecheck_expr(minusone, ctxt), INTEGER_TYPE)

        formula_str = """
(declare-const y Int)
(declare-const v Bool)
(assert (ite v false (= y (- 1))))
(check-sat)
"""
        formula, globals = parse_str(formula_str)
        ite = formula.commands[2].term
        ctxt = Context(globals, {})
        self.assertEqual(typecheck_expr(ite, ctxt), BOOLEAN_TYPE)

    def test_error(self):
        formula_str = """
(declare-const y Int)
(declare-const v Bool)
(assert (= v (not (= v (- 1)))))
(check-sat)
"""
        formula, globals = parse_str(formula_str)
        ctxt = Context(globals, {})
        equals = formula.commands[2].term
        try:
            typecheck_expr(equals, ctxt)
        except Exception:
            no_except = False
        self.assertFalse(no_except)

    def test_typecheck_nary_int_ret(self):
        formula_str = """
(declare-const v Int)
(declare-const w Int)
(assert (= v (+ v v w)))
(check-sat)
"""
        formula, globals = parse_str(formula_str)
        ctxt = Context(globals, {})
        nary_plus = formula.commands[2].term.subterms[1]
        self.assertEqual(typecheck_expr(nary_plus, ctxt), INTEGER_TYPE)

    def test_typecheck_comp_ops(self):
        formula_str = """
(declare-const v Int)
(declare-const w Int)
(assert (> v (+ v v w)))
(check-sat)
"""
        formula, globals = parse_str(formula_str)
        greater = formula.commands[2].term
        ctxt = Context(globals, {})
        self.assertEqual(typecheck_expr(greater, ctxt), BOOLEAN_TYPE)

    def test_typecheck_string_ops(self):
        formula_str = """
(assert (distinct (str.replace_all "B" "A" "") "B"))
(check-sat)
"""
        formula, globals = parse_str(formula_str)
        ctxt = Context(globals, {})
        distinct = formula.commands[0].term
        self.assertEqual(typecheck_expr(distinct, ctxt), BOOLEAN_TYPE)
        str_repl = distinct.subterms[0]
        self.assertEqual(typecheck_expr(str_repl, ctxt), STRING_TYPE)
        formula_str = """
(declare-fun a () String)
(assert (str.contains (str.substr a 0 (- (str.len a) 1)) "A"))
(assert (= (ite (= (str.at a 0) "B") 1 0) (ite (= (str.at a 0) "A") 1 0) 0))
(assert (= (str.at a (- (str.len a) 1)) "B"))
(check-sat)
"""
        formula, globals = parse_str(formula_str)
        ctxt = Context(globals, {})
        for i in range(1, 4):
            typecheck_expr(formula.commands[i].term, ctxt)

    def test_typechecking_formula_small(self):
        formula_str = """
(declare-fun x () Int)
(declare-fun y () Int)
(declare-fun z () Int)
(assert (> (* (+ 3 x) (- y 2)) (/ 5 z)))
(check-sat)
"""
        formula, glob = parse_str(formula_str)
        typecheck(formula, glob)
        self.assertEqual(oracle(formula), True)

    def test_typechecking_formula_large(self):
        script_path = pathlib.Path(__file__).parent.absolute()
        formula, glob = parse_file(
            str(script_path) + "/test.smt2", silent=False
        )
        typecheck(formula, glob)
        oracle(formula)
        self.assertEqual(oracle(formula), True)


if __name__ == "__main__":
    TypecheckerTestCase.test_typechecker()
    unittest.main()
