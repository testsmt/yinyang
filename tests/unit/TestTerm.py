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

import sys
import unittest

from src.parsing.Parse import parse_str
from src.parsing.Ast import Const, Var, Expr

sys.path.append("../../")


class TermTestCase(unittest.TestCase):
    def test_term(self):
        formula1 = """\
(declare-const y Int)
(declare-const v Bool)
(assert (= v (not (= y (- 1)))))
(assert (ite v false (= y (- 1))))
(check-sat)
"""
        formula2 = """\
(declare-const x Int)
(declare-const y Int)
(assert (= (+ x y) y))
"""

        def var2const():
            script, _ = parse_str(formula1)
            script.commands[2].term.substitute(
                Var(name="v", type="Bool"), Const(name="true", type="Bool")
            )
            self.assertEqual(
                script.commands[2].term.__str__(), "(= true (not (= y (- 1))))"
            )

        def entire_expr():
            assert_expr = parse_str(formula2)[0].commands[2].term
            z = Var("z", "Int")
            y = Var("y", "Int")
            assert_expr.substitute(assert_expr, Expr("-", [z, y]))
            self.assertEqual(assert_expr.__str__(), "(- z y)")

        def subexpr():
            z = Var("z", "Int")
            y = Var("y", "Int")
            assert_expr = parse_str(formula2)[0].commands[2].term
            assert_expr.substitute(assert_expr.subterms[0], Expr("-", [z, y]))
            self.assertEqual(assert_expr.__str__(), "(= (- z y) y)")

        def substitute1():
            formula = """\
(declare-const x String)
(declare-const y String)
(declare-const z String)
(declare-const c String)
(assert (= x (str.substr z 0 (str.len x))))
            """
            expr = parse_str(formula)[0].commands[4].term
            x = Var("x", "String")
            var1 = Var("var1", "String")
            expr.substitute(x, var1)
            self.assertEqual(
                expr.__str__(), "(= var1 (str.substr z 0 (str.len var1)))")

        def substitute2():
            formula = """\
(declare-const x String)
(declare-const y String)
(declare-const z String)
(assert (= z (str.++ x y)))
(assert (= x (str.substr z 0 (str.len x))))
(assert (= y (str.replace z x (str.at z (str.len z)))))
            """
            formula, _ = parse_str(formula)
            equals = formula.commands[5].term
            replacee = formula.commands[3].term.subterms[1]
            z = Var("z", "String")
            equals.substitute(z, replacee)
            expected = """\
(= y (str.replace (str.++ x y) x (str.at (str.++ x y) (str.len (str.++ x y)))))
"""
            self.assertEqual(equals.__str__().strip(), expected.strip())

        def free_vars_quantifier():
            script = """\
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun a () Real)
(declare-fun ts0uscore1 () Real)
(assert (exists ((ts0uscore1 Real)) (> ts0uscore1 a)))
(check-sat)
"""
            script, _ = parse_str(script)
            self.assertEqual(script.free_var_occs.__str__(), "[a:Real]")

            script = """\
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun a () Real)
;(declare-fun ts0uscore1 () Real)
(assert (exists ((ts0uscore1 Real)) (> ts0uscore1 a)))
(check-sat)
"""
            script, _ = parse_str(script)
            self.assertEqual(script.free_var_occs.__str__(), "[a:Real]")

            script = """\
(set-info :category "industrial")
(set-info :status unsat)
(declare-fun a () Real)
(declare-fun ts0uscore1 () Real)
(assert (> ts0uscore1 a))
(check-sat)
"""
            script, _ = parse_str(script)
            self.assertEqual(
                script.free_var_occs.__str__(), "[ts0uscore1:Real, a:Real]"
            )

        def free_vars_let():
            script_str = """\
(declare-fun ?v_0 () Int)
(assert (let ((?v_0 (+ (* 4 f3) 1))) (= ?v_0 0)))
(check-sat)
(exit)
"""
            script, _ = parse_str(script_str)
            self.assertEqual(script.free_var_occs.__str__(), "[]")

            script_str = """\
(declare-fun ?v_0 () Int)
(assert (= ?v_0 0))
(check-sat)
(exit)
"""
            script, _ = parse_str(script_str)
            self.assertEqual(script.free_var_occs.__str__(), "[?v_0:Int]")

        def free_vars_let2():
            script_str = """\
(declare-fun ?v_0 () Int)
(assert (= ?v_0 0))
(assert (let ((?v_0 (+ (* 4 f3) 1))) (= ?v_0 0)))
(check-sat)
(exit)
"""
            script, _ = parse_str(script_str, silent=False)
            self.assertEqual(script.free_var_occs.__str__(), "[?v_0:Int]")

            script_str = """\
(declare-fun ?v_0 () Int)
(assert (let ((?v_0 (+ (* 4 f3) 1))) (= ?v_0 0)))
(assert (= ?v_0 0))
(check-sat)
(exit)
"""
            script, _ = parse_str(script_str, silent=False)
            self.assertEqual(script.free_var_occs.__str__(), "[?v_0:Int]")

            script_str = """\
(declare-fun ?v_0 () Int)
(assert (let ((?v_0 (+ (* 4 f3) 1))) (= ?v_0 0)))
(assert (= ?v_0 0))
(check-sat)
(exit)
"""
            script, _ = parse_str(script_str, silent=False)
            self.assertEqual(script.free_var_occs.__str__(), "[?v_0:Int]")

        var2const()
        entire_expr()
        subexpr()
        substitute1()
        substitute2()
        free_vars_quantifier()
        free_vars_let()
        free_vars_let2()


if __name__ == "__main__":
    TermTestCase().test_term()
