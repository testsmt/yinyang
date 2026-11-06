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

import random

from yinyang.src.parsing.Parse import parse_file, parse_str
from yinyang.src.parsing.Typechecker import typecheck
from yinyang.src.mutators.SemanticFusion.SemanticFusion import SemanticFusion
from yinyang.src.mutators.SemanticFusion.VariableFusion import (
    canonicalize_script
)

sys.path.append("../../")


class Mockargs:
    oracle = ""
    config = ""
    generate_functions = 0
    multiple_variables = 2


class SemanticFusionTestCase(unittest.TestCase):
    def test_sf_sat(self):
        fn1 = "tests/res/formula1.smt2"
        fn2 = "tests/res/formula2.smt2"
        fn_fcts = "tests/res/fusion_functions.txt"

        args = Mockargs()
        args.oracle = "sat"
        args.config = fn_fcts
        script1, _ = parse_file(fn1, silent=True)
        script2, _ = parse_file(fn2, silent=True)
        sf_sat = SemanticFusion(script1, script2, args)
        args.oracle = "unsat"
        script1, _ = parse_file(fn1, silent=True)
        script2, _ = parse_file(fn2, silent=True)
        sf_sat.mutate()

    def fuse(self, formula1, formula2, oracle="sat", seeds=range(10)):
        """
        Fuse the two formulas with each random seed. Each mutant must parse
        and typecheck, and declare each symbol once.
        :returns: the mutants as strings
        """
        args = Mockargs()
        args.oracle = oracle
        args.config = "yinyang/config/fusion_functions.txt"
        mutants = []
        for seed in seeds:
            random.seed(seed)
            script1, _ = parse_str(formula1)
            script2, _ = parse_str(formula2)
            fused, success, _ = SemanticFusion(
                script1, script2, args).mutate()
            self.assertTrue(success)
            mutant = str(fused)
            script, glob = parse_str(mutant)
            typecheck(script, glob)
            symbols = [
                cmd.symbol for cmd in script.commands
                if hasattr(cmd, "symbol")
            ]
            self.assertEqual(len(symbols), len(set(symbols)), mutant)
            mutants.append(mutant)
        return mutants

    def test_define_fun(self):
        # Definitions of both formulas are kept and renamed with their
        # bodies; parameters and bound variables are not renamed.
        formula = """
        (declare-fun a () Int)
        (declare-fun f (Int) Int)
        (define-fun p () Bool (> (f a) 0))
        (define-fun g ((x Int) (a Int)) Int (+ x a))
        (define-fun-rec fact ((k Int)) Int
          (ite (<= k 0) 1 (* k (fact (- k 1)))))
        (define-const m Int (+ a 1))
        (assert (and p (> (fact m) 0)))
        (assert (forall ((a Int)) (> (g a 1) (f a))))
        (check-sat)
        """
        for oracle in ["sat", "unsat"]:
            for mutant in self.fuse(formula, formula, oracle):
                for prefix in ["scr1_", "scr2_"]:
                    self.assertIn(
                        "(define-fun %sp () Bool (> (%sf " % (prefix, prefix),
                        mutant)
                    self.assertIn(
                        "(define-fun %sg ((x Int) (a Int)) Int (+ x a))"
                        % prefix, mutant)
                    self.assertIn("(define-fun-rec %sfact " % prefix, mutant)
                    self.assertIn("(%sfact (- k 1))" % prefix, mutant)
                    self.assertIn("(define-const %sm Int (+ " % prefix,
                                  mutant)
                    self.assertIn(
                        "(forall ((a Int)) (> (%sg a 1) (%sf a)))"
                        % (prefix, prefix), mutant)

    def test_quoted_symbols(self):
        # The prefix goes inside the bars of quoted symbols, also in the
        # names of the fused variables.
        formula = """
        (declare-fun |x y| () Int)
        (declare-fun c () Int)
        (assert (> |x y| c))
        (check-sat)
        """
        for oracle in ["sat", "unsat"]:
            for mutant in self.fuse(formula, formula, oracle):
                self.assertIn("(declare-fun |scr1_x y| () Int)", mutant)
                self.assertIn("(declare-fun |scr2_x y| () Int)", mutant)
                self.assertNotIn("_|", mutant)
                self.assertNotIn("|_", mutant)

    def test_named_and_datatypes(self):
        # :named terms are renamed; a datatype declared by both formulas
        # is declared once.
        formula = """
        (declare-datatypes ((L 0)) (((nil) (cons (hd Int) (tl L)))))
        (declare-const l L)
        (declare-const v Int)
        (assert (! (and ((_ is cons) l) (> (hd l) v)) :named h1))
        (check-sat)
        """
        for mutant in self.fuse(formula, formula):
            self.assertEqual(mutant.count("(declare-datatypes"), 1)
            self.assertIn(":named scr1_h1", mutant)
            self.assertIn(":named scr2_h1", mutant)

    def test_definitions_after_assert(self):
        # The combined assert comes after definitions that follow the
        # first assert of a formula.
        formula = """
        (declare-fun a () Int)
        (declare-fun b () Int)
        (assert (> a b))
        (define-fun p () Bool (< a 10))
        (assert p)
        (check-sat)
        """
        for mutant in self.fuse(formula, formula):
            self.assertLess(mutant.index("(define-fun scr2_p"),
                            mutant.index("(assert"))

    def test_bitvectors(self):
        # Fusion of bit-vector variables used to crash in
        # fusion_contraints.
        formula = """
        (declare-fun x () (_ BitVec 8))
        (declare-fun y () (_ BitVec 8))
        (assert (bvult x y))
        (check-sat)
        """
        for oracle in ["sat", "unsat"]:
            self.fuse(formula, formula, oracle)

    def test_sort_clash(self):
        # Sorts are not renamed: formulas that declare the same sort
        # differently are not fused.
        args = Mockargs()
        args.oracle = "sat"
        args.config = "yinyang/config/fusion_functions.txt"
        script1, _ = parse_str("""
        (declare-datatypes ((T 0)) (((a) (b))))
        (declare-const x Int)
        (declare-const t T)
        (assert (and (> x 0) (= t a)))
        """)
        script2, _ = parse_str("""
        (declare-datatypes ((T 0)) (((a) (b) (c))))
        (declare-const y Int)
        (declare-const t T)
        (assert (and (> y 0) (= t c)))
        """)
        _, success, _ = SemanticFusion(script1, script2, args).mutate()
        self.assertFalse(success)

    def test_canonicalize_keeps_order(self):
        # Only declarations after the first assert are moved before it.
        script, _ = parse_str("""
        (declare-const a Int)
        (define-fun p () Bool (> a 0))
        (assert p)
        (declare-const b Int)
        (assert (> b 0))
        """)
        commands = [str(cmd) for cmd in canonicalize_script(script).commands]
        self.assertEqual(commands[:4], [
            "(declare-const a Int)", "(define-fun p () Bool (> a 0))",
            "(declare-const b Int)", "(assert p)"])


if __name__ == "__main__":
    unittest.main()
