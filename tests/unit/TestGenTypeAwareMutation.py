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

import copy
import random
import unittest
import sys

sys.path.append("../../")
import os

from yinyang.src.parsing.Parse import *
from yinyang.src.parsing.Typechecker import Context, typecheck
from yinyang.src.mutators.GenTypeAwareMutation.GenTypeAwareMutation import *
from yinyang.src.mutators.GenTypeAwareMutation.Operator import Operator
from yinyang.src.mutators.GenTypeAwareMutation.Util import *


class Mockargs:
    modulo = 3
    config = "yinyang/config/typefuzz_config.txt"


class GenTypeAwareMutationTestCase(unittest.TestCase):
    def test_ta(self):
        formulafile = "formula.smt2"
        formula = """
        (declare-fun x () Int)
        (declare-fun y () Int)
        (declare-fun z () Int)
        (assert (> (* (+ 3 x) (- y 2)) (div 5 z)))
        (assert (= (+ 7 y) x))
        (assert (< 6 (div (+ 4 x) z)))
        (check-sat)
        """
        with open(formulafile, "w") as f:
            f.write(formula)
        script, glob = parse_str(formula)
        typecheck(script, glob)
        args = Mockargs()
        args.name = formulafile.strip(".smt2")
        script, glob = parse_file(formulafile, silent=True)
        typecheck(script, glob)
        self.av_expr, self.expr_type = get_all_subterms(script)
        unique_expr = get_unique_subterms(script)
        gen = GenTypeAwareMutation(script, args, unique_expr)
        gen.generate()
        os.system("rm " + formulafile)

    def test_issue31_nullary_regex_op(self):
        # re.none, re.all, and re.allchar are 0-ary regex constants, not
        # function applications: the generated replacement must print as
        # a bare "re.none" rather than "(re.none )".
        formula = """
        (declare-fun s () String)
        (assert (str.in_re s re.none))
        (check-sat)
        """
        script, glob = parse_str(formula)
        typecheck(script, glob)
        args = Mockargs()
        args.name = "formula"
        unique_expr = get_unique_subterms(script)
        gen = GenTypeAwareMutation(script, args, unique_expr)

        regexp_term = script.assert_cmd[0].term.subterms[1]

        for op_name in ("re.none", "re.all", "re.allchar"):
            op = Operator(op_name, ["RegLan"], [])
            gen.get_candidate_ops = lambda term, op=op: [op]
            replacee = gen.get_replacee(regexp_term)
            self.assertIsNotNone(replacee)
            self.assertTrue(replacee.is_const)
            self.assertEqual(replacee.__str__(), op_name)

    def test_all_sorts(self):
        # Terms of any sort can be mutated, not only Bool, Int, Real,
        # String, RegLan and RoundingMode. Each sort, e.g. each bit-vector
        # width, is a type of its own, so mutants stay well-typed.
        formulas = [
            "(declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))"
            "(declare-fun z () (_ BitVec 4))(assert (bvult (bvadd x y) x))"
            "(assert (= ((_ extract 3 0) x) (bvor z #x1)))",
            "(declare-fun a () Float32)(declare-fun b () Float32)"
            "(assert (fp.lt (fp.add RNE a b) (fp.mul RTZ a a)))",
            "(declare-fun m () (Array Int Int))(declare-fun i () Int)"
            "(assert (= (select (store m i 1) 0) (select m (+ i 1))))",
            "(declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))"
            "(declare-fun l () L)(assert (= (tl (cons 1 l)) nil))"
            "(assert (> (hd l) (hd (tl l))))",
            "(declare-sort U 0)(declare-fun f (U) U)(declare-fun u () U)"
            "(assert (distinct (f u) (f (f u)) u))",
        ]
        random.seed(0)
        args = Mockargs()
        for formula in formulas:
            script, glob = parse_str(formula, silent=False)
            typecheck(script, glob)
            unique_expr = get_unique_subterms(copy.deepcopy(script))
            gen = GenTypeAwareMutation(script, args, unique_expr)
            mutated = 0
            for _ in range(30):
                mutant, success, _ = gen.mutate()
                if not success:
                    continue
                mutated += 1
                reparsed, glob2 = parse_str(mutant.__str__(), silent=False)
                self.assertIsNotNone(reparsed, mutant.__str__())
                typecheck(reparsed, glob2)  # raises if ill-typed
            self.assertGreater(mutated, 0, formula)

        script, glob = parse_str(formulas[0])
        typecheck(script, glob)
        unique_expr = get_unique_subterms(script)
        # x, y, (bvadd x y)
        self.assertEqual(len(unique_expr["(_ BitVec 8)"]), 3)
        # ((_ extract 3 0) x), z, #x1, (bvor z #x1)
        self.assertEqual(len(unique_expr["(_ BitVec 4)"]), 4)


if __name__ == "__main__":
    unittest.main()
