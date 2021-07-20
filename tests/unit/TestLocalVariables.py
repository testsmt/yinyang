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
import os

sys.path.append("../../")

from src.parsing.parse import *
from src.parsing.typechecker import Context, typecheck
from src.generators.TypeAwareOpMutation import TypeAwareOpMutation
from src.generators.GenTypeAwareMutation.GenTypeAwareMutation import *
from src.generators.GenTypeAwareMutation.Util import *


class Mockargs:
    modulo = 3
    config_file = "config/generalization.txt"


class LocalVariableMutationTestCase(unittest.TestCase):
    def test_local_defs_quantifier(self):
        formula = """
        (declare-fun |old(~a10~0)| () Int)
        (declare-fun ~a1~0 () Int)
        (assert (not (and (exists ((v_prenex_1 Int)) (and (not (= 0 (mod v_prenex_1 5))) (< v_prenex_1 0) (<= v_prenex_1 218) (<= (+ (div v_prenex_1 5) 449583) ~a1~0) (< 38 v_prenex_1))) (<= 2 |old(~a10~0)|))))
        (assert (not (and (<= 2 |old(~a10~0)|) (exists ((v_prenex_2 Int)) (and (<= (+ (div v_prenex_2 5) 449582) ~a1~0) (< 218 v_prenex_2) (<= 0 v_prenex_2))))))
        (assert (not (and (<= 3 |old(~a10~0)|) (exists ((v_prenex_4 Int)) (and (<= (+ (div v_prenex_4 5) 449582) ~a1~0) (= 0 (mod v_prenex_4 5)) (<= (+ v_prenex_4 13) 0))))))
        (assert (not (and (exists ((v_prenex_5 Int)) (and (<= 0 v_prenex_5) (<= (+ (div v_prenex_5 5) 449582) ~a1~0) (< 38 v_prenex_5) (<= v_prenex_5 218))) (<= 2 |old(~a10~0)|))))
        (assert (not (and (exists ((v_prenex_3 Int)) (and (= 0 (mod v_prenex_3 5)) (< 38 v_prenex_3) (<= (+ (div v_prenex_3 5) 449582) ~a1~0) (<= v_prenex_3 218))) (<= 2 |old(~a10~0)|))))
        (assert (and (<= 3 |old(~a10~0)|) (exists ((v_prenex_6 Int)) (and (<= (+ v_prenex_6 13) 0) (< v_prenex_6 0) (not (= 0 (mod v_prenex_6 5))) (<= (+ (div v_prenex_6 5) 449583) ~a1~0)))))
        (check-sat)
        (exit)
        """  # noqa: E501
        formula, glob = parse_str(formula)
        typecheck(formula, glob)
        loc1 = formula.assert_cmd[0].term.subterms[0].subterms[0]
        loc1_sub = loc1.subterms[0]
        not_loc = formula.assert_cmd[0].term.subterms[0].subterms[1]
        loc2 = formula.assert_cmd[1].term.subterms[0].subterms[1].subterms[0]
        if not local_compatible(loc1_sub, loc1):
            return False
        if not local_compatible(not_loc, loc1):
            return False
        if local_compatible(loc1, loc2):
            return False
        return True

    def test_local_defs_let(self):
        formula = """
        (declare-fun skoX () Real)
        (declare-fun skoS () Real)
        (declare-fun skoC () Real)
        (assert (let ((?v_2 (<= skoX 0))(?v_0 (* skoC (/ (- 235) 42)))) (let ((?v_1 (<= ?v_0 skoS))) (and (<= (* skoX (+ (/ (- 207) 6250000) (* skoX (/ 207 207)))) (/ (- 69) 250)) (and (not ?v_1) (and (or (not (<= skoS ?v_0)) ?v_2) (and (or ?v_1 ?v_2) (and (= (* skoS skoS) (+ 1 (* skoC (* skoC (- 1))))) (and (<= skoX 289) (<= 0 skoX))))))))))
        (check-sat)
        (exit)
        """  # noqa: E501
        formula, glob = parse_str(formula)
        typecheck(formula, glob)
        let1 = formula.assert_cmd[0].term
        let2 = let1.subterms[0]
        let2_sub = let2.subterms[0]
        if local_compatible(let1, let2):
            return False
        if not local_compatible(let2, let1):
            return False
        if local_compatible(let2, let2_sub):
            return False
        return True

    def test_local_defs_simple(self):
        formula1 = """
        (declare-fun a () Real)
        (assert (exists ((ts0uscore1 Real)) (> ts0uscore1 a)))
        (check-sat)
        """
        formula1, glob = parse_str(formula1)
        typecheck(formula1, glob)
        declare = formula1.assert_cmd[0].term
        sub = declare.subterms[0]
        if local_compatible(declare, sub):
            return False
        if not local_compatible(sub, declare):
            return False
        formula2 = """
        (declare-fun f3 () Int)
        (assert (let ((?v_0 (+ (* 4 f3) 1))) (= ?v_0 0)))
        (check-sat)
        (exit)
        """
        formula2, glob = parse_str(formula2)
        typecheck(formula2, glob)
        declare = formula2.assert_cmd[0].term
        sub1 = declare.subterms[0].subterms[0]
        sub2 = declare.subterms[0].subterms[1]
        if not local_compatible(sub1, sub2):
            return False
        if local_compatible(declare, sub1):
            return False
        return True

    def test_parent_pointer(self):
        formula = """
        (declare-fun skoX () Real)
        (declare-fun skoS () Real)
        (declare-fun skoC () Real)
        (assert (let ((?v_2 (<= skoX 0))(?v_0 (* skoC (/ (- 235) 42)))) (let ((?v_1 (<= ?v_0 skoS))) (and (<= (* skoX (+ (/ (- 207) 6250000) (* skoX (/ 207 207)))) (/ (- 69) 250)) (and (not ?v_1) (and (or (not (<= skoS ?v_0)) ?v_2) (and (or ?v_1 ?v_2) (and (= (* skoS skoS) (+ 1 (* skoC (* skoC (- 1))))) (and (<= skoX 289) (<= 0 skoX))))))))))
        (check-sat)
        (exit)
        """  # noqa: E501
        formula, glob = parse_str(formula)
        typecheck(formula, glob)
        av_expr, expr_type = get_all_subterms(formula)
        for t in av_expr:
            if t.subterms:
                for sub in t.subterms:
                    if sub.parent != t:
                        return False
        return True

    def test_type_mutation_local(self):
        formula = """
        (declare-fun skoX () Real)
        (declare-fun skoS () Real)
        (declare-fun skoC () Real)
        (assert (let ((?v_2 (<= skoX 0))(?v_0 (* skoC (/ (- 235) 42)))) (let ((?v_1 (<= ?v_0 skoS))) (and (<= (* skoX (+ (/ (- 207) 6250000) (* skoX (/ 207 207)))) (/ (- 69) 250)) (and (not ?v_1) (and (or (not (<= skoS ?v_0)) ?v_2) (and (or ?v_1 ?v_2) (and (= (* skoS skoS) (+ 1 (* skoC (* skoC (- 1))))) (and (<= skoX 289) (<= 0 skoX))))))))))
        (check-sat)
        (exit)
        """  # noqa: E501
        formula, glob = parse_str(formula)
        typecheck(formula, glob)
        av_expr, expr_type = get_all_subterms(formula)
        unique_expr = get_unique_subterms(formula)
        args = Mockargs()
        gen = GenTypeAwareMutation(formula, args, unique_expr)
        gen.generate()


if __name__ == "__main__":
    unittest.main()
