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

from yinyang.src.parsing.Parse import parse_str
from yinyang.src.parsing.Typechecker import typecheck
from yinyang.src.parsing.Logic import (
    parse_logic, logic_name, infer_logic, divides_by_zero,
    is_real_logic, numerals_to_decimals, DIV_BY_ZERO_MODES,
)
from yinyang.src.core.Fuzzer import Fuzzer

sys.path.append("../../")


def infer(formula, div_by_zero="nonlinear"):
    script, _ = parse_str(formula, silent=False)
    return set(infer_logic(script, div_by_zero))


class Args:
    logic_mode = "widen"
    div_by_zero = "nonlinear"
    keep_mutants = True  # read by Fuzzer.__del__


def make_fuzzer(logic_mode, div_by_zero="nonlinear"):
    # Bypass Fuzzer.__init__, which sets up logging and folders.
    fuzzer = Fuzzer.__new__(Fuzzer)
    fuzzer.args = Args()
    fuzzer.args.logic_mode = logic_mode
    fuzzer.args.div_by_zero = div_by_zero
    fuzzer.current_logic = None
    return fuzzer


INT_XY = "(declare-fun x () Int)(declare-fun y () Int)"
REAL_R = "(declare-fun r () Real)"


class LogicTestCase(unittest.TestCase):
    def test_parse_logic(self):
        self.assertEqual(parse_logic("QF_LIA"), {"I"})
        self.assertEqual(parse_logic("QF_AUFNIRA"),
                         {"A", "UF", "I", "R", "NL"})
        self.assertEqual(parse_logic("UFDTLIA"), {"Q", "UF", "DT", "I"})
        self.assertEqual(parse_logic("QF_SLIA"), {"S", "I"})
        self.assertEqual(parse_logic("QF_ABVFP"), {"A", "BV", "FP"})
        self.assertEqual(parse_logic("QF_IDL"), {"I"})
        self.assertEqual(parse_logic("QF_UF"), {"UF"})
        self.assertEqual(parse_logic("LRA"), {"Q", "R"})
        self.assertIsNone(parse_logic("ALL"))
        self.assertIsNone(parse_logic("QF_"))
        self.assertIsNone(parse_logic("HORN"))

    def test_logic_name(self):
        for name in ["QF_LIA", "QF_AUFNIRA", "UFDTLIA", "QF_SLIA", "QF_BV",
                     "QF_ABVFP", "QF_UF", "LRA", "QF_BVFPLRA", "AUFLIRA"]:
            self.assertEqual(logic_name(parse_logic(name)), name)
        self.assertEqual(logic_name(frozenset()), "QF_UF")
        self.assertEqual(logic_name(frozenset({"Q"})), "UF")
        self.assertEqual(logic_name(parse_logic("QF_IDL")), "QF_LIA")

    def test_numerals_to_decimals(self):
        # In real logics numerals are reals; written as decimals they stay
        # reals when a mutant needs a logic with integers (or ALL).
        self.assertTrue(is_real_logic("QF_UFNRA"))
        self.assertTrue(is_real_logic("QF_RDL"))
        for name in ["QF_NIRA", "QF_LIA", "ALL", "QF_BV", None]:
            self.assertFalse(is_real_logic(name))
        script, glob = parse_str(
            "(set-logic QF_UFNRA)"
            "(declare-fun f (Real Real) Real)(declare-fun x () Real)"
            "(declare-fun c () Bool)"
            "(define-fun g ((d Real)) Real (+ d 2))"
            "(assert (let ((y 3)) (> (f (* 25 x) 16) (ite c x y))))"
            "(assert (= (g 0) (/ 1 3) 1.5))")
        numerals_to_decimals(script)
        typecheck(script, glob)
        self.assertEqual(str(script).split("\n")[3:], [
            "(define-fun g ((d Real)) Real (+ d 2.0))",
            "(assert (let ((y 3.0)) (> (f (* 25.0 x) 16.0) (ite c x y))))",
            "(assert (= (g 0.0) (/ 1.0 3.0) 1.5))",
        ])
        self.assertEqual(infer_logic(script), {"UF", "R"})

    def test_logic_name_strings(self):
        # The only logics with strings are QF_S, QF_SLIA and QF_SNIA; z3
        # does not know other names such as QF_SNRA (no String sort).
        for name in ["QF_S", "QF_SLIA", "QF_SNIA"]:
            self.assertEqual(logic_name(parse_logic(name)), name)
        self.assertEqual(logic_name(frozenset({"S", "NL", "I"})), "QF_SNIA")
        for features in [{"S", "R", "NL"}, {"S", "I", "Q"}, {"S", "I", "UF"},
                         {"S", "BV"}, {"S", "A", "I"}, {"S", "I", "R"},
                         {"S", "FP"}, {"S", "DT"}]:
            self.assertEqual(logic_name(frozenset(features)), "ALL")

    def test_linear(self):
        self.assertEqual(infer(INT_XY + "(assert (= (* 2 x) y))"), {"I"})
        self.assertEqual(infer(INT_XY + "(assert (= (* x 2 3) y))"), {"I"})
        self.assertEqual(infer(INT_XY + "(assert (= (* (- 2) x) y))"), {"I"})
        self.assertEqual(infer(INT_XY + "(assert (= (div x 3) y))"), {"I"})
        self.assertEqual(infer(INT_XY + "(assert (= (abs x) y))"), {"I"})
        self.assertEqual(
            infer(INT_XY + "(assert (let ((c 2)) (= (* c x) y)))"), {"I"})
        self.assertEqual(infer(REAL_R + "(assert (= (* (/ 1 2) r) r))"),
                         {"R"})
        self.assertEqual(infer(REAL_R + "(assert (= (/ r 2) r))"), {"R"})

    def test_nonlinear(self):
        self.assertIn("NL", infer(INT_XY + "(assert (= (* x y) 6))"))
        self.assertIn("NL", infer(INT_XY + "(assert (= (div x y) 6))"))
        self.assertIn("NL", infer(INT_XY + "(assert (= (mod x y) 6))"))
        self.assertIn("NL", infer(REAL_R + "(assert (= (/ 1 r) 6.0))"))
        # z3 rejects non-literal coefficients in linear logics.
        self.assertIn("NL", infer(INT_XY + "(assert (= (* (+ 1 2) x) 6))"))
        self.assertIn(
            "NL", infer(INT_XY + "(assert (let ((c y)) (= (* c x) 6)))"))

    def test_arithmetic_sorts(self):
        self.assertEqual(infer(INT_XY + "(assert (> x 1.5))"), {"I", "R"})
        self.assertEqual(infer(REAL_R + "(assert (> (to_int r) 1))"),
                         {"I", "R"})
        self.assertEqual(
            infer("(assert (forall ((q Int)) (> q 0)))"), {"Q", "I"})

    def test_theories(self):
        self.assertEqual(
            infer("(declare-fun b () (_ BitVec 8))"
                  "(assert (= ((_ extract 3 0) b) #x1))"), {"BV"})
        self.assertEqual(
            infer("(declare-fun a () (Array Int Int))"
                  "(assert (= (select a 1) 2))"), {"A", "I"})
        self.assertEqual(
            infer("(declare-fun s () String)"
                  "(assert (= (str.++ s \"a\") \"ba\"))"), {"S"})
        self.assertEqual(
            infer("(declare-fun f () Float32)"
                  "(assert (fp.isZero (fp.add RNE f f)))"), {"FP"})
        self.assertEqual(
            infer("(declare-sort U 0)(declare-fun u () U)(assert (= u u))"),
            {"UF"})
        self.assertEqual(
            infer(INT_XY + "(declare-fun f (Int) Int)(assert (= (f x) y))"),
            {"UF", "I"})
        self.assertEqual(
            infer("(declare-datatypes ((L 0)) (((nil) (cons (hd Int) "
                  "(tl L)))))(declare-fun l () L)(assert (= l nil))"),
            {"DT", "I"})
        # Macros do not need UF.
        self.assertEqual(
            infer(INT_XY + "(define-fun g ((z Int)) Int (+ z 1))"
                  "(assert (= (g x) y))"), {"I"})

    def test_prepare_seed(self):
        script, _ = parse_str(
            "(set-option :produce-models true)(set-logic QF_LIA)"
            "(set-info :status sat)(declare-fun echo_x () Int)"
            "(declare-fun simplify_y () Int)(assert (> echo_x simplify_y))"
            "(check-sat)(get-model)(get-value (echo_x))(echo \"hi\")(exit)"
        )
        self.assertEqual(script.logic, "QF_LIA")
        self.assertEqual(
            script.__str__(),
            "(set-option :produce-models true)\n"
            "(declare-fun echo_x () Int)\n"
            "(declare-fun simplify_y () Int)\n"
            "(assert (> echo_x simplify_y))\n"
            "(check-sat)\n"
            "(exit)",
        )
        script, _ = parse_str(INT_XY + "(assert (= x y))")
        self.assertIsNone(script.logic)

    def test_mutant_logic(self):
        seed, _ = parse_str("(set-option :produce-models true)"
                            "(set-logic QF_LIA)" + INT_XY +
                            "(assert (= (* 2 x) y))(check-sat)")
        linear, _ = parse_str(INT_XY + "(assert (= (+ 2 x) y))")
        nonlinear, _ = parse_str(INT_XY + "(assert (= (* y x) y))")

        fuzzer = make_fuzzer("widen")
        fuzzer.init_logic([seed])
        self.assertEqual(fuzzer.mutant_logic(linear), ("QF_LIA", True))
        self.assertEqual(fuzzer.mutant_logic(nonlinear), ("QF_NIA", True))
        fuzzer.current_logic = "QF_LIA"
        self.assertEqual(
            fuzzer.script_str(seed).split("\n")[:2],
            ["(set-option :produce-models true)", "(set-logic QF_LIA)"])

        fuzzer = make_fuzzer("skip")
        fuzzer.init_logic([seed])
        self.assertEqual(fuzzer.mutant_logic(linear), ("QF_LIA", True))
        self.assertEqual(fuzzer.mutant_logic(nonlinear), (None, False))

        fuzzer = make_fuzzer("strip")
        fuzzer.init_logic([seed])
        self.assertEqual(fuzzer.mutant_logic(nonlinear), (None, True))
        self.assertNotIn("set-logic", fuzzer.script_str(seed))

    def test_random_all(self):
        # With --random-all, about half of the mutants get ALL instead of
        # their logic; not for logics yinyang does not understand, and not
        # for scripts declaring a sort that is built in under ALL.
        import random
        seed, _ = parse_str("(set-logic QF_LIA)" + INT_XY
                            + "(assert (= x y))")
        fuzzer = make_fuzzer("widen")
        fuzzer.args.random_all = True
        fuzzer.init_logic([seed])
        random.seed(1)
        logics = [fuzzer.random_all("QF_LIA", seed) for _ in range(200)]
        self.assertEqual(set(logics), {"QF_LIA", "ALL"})
        self.assertTrue(60 < logics.count("ALL") < 140)
        self.assertIsNone(fuzzer.random_all(None, seed))

        set_sort, _ = parse_str("(set-logic QF_UF)(declare-sort Set 0)"
                                "(declare-const a Set)(assert (= a a))")
        fuzzer.init_logic([set_sort])
        self.assertEqual({fuzzer.random_all("QF_UF", set_sort)
                          for _ in range(50)}, {"QF_UF"})

        horn, _ = parse_str("(set-logic HORN)" + INT_XY + "(assert (= x y))")
        fuzzer.init_logic([horn])
        self.assertEqual({fuzzer.random_all("HORN", horn)
                          for _ in range(50)}, {"HORN"})

        fuzzer.args.random_all = False
        fuzzer.init_logic([seed])
        self.assertEqual({fuzzer.random_all("QF_LIA", seed)
                          for _ in range(50)}, {"QF_LIA"})

    def test_div_by_zero(self):
        # Division by a literal zero is undefined in SMT-LIB; cvc5 rejects
        # it in linear logics ("A non-linear fact was asserted to
        # arithmetic in a linear logic"), z3 accepts it.
        for formula in [
            INT_XY + "(assert (= (mod x 0) y))",
            INT_XY + "(assert (= (div x (- 0)) y))",
            REAL_R + "(assert (= (/ r 0.0) r))",
            REAL_R + "(assert (= (/ r 2 0.00) r))",
        ]:
            self.assertIn("NL", infer(formula), formula)
            self.assertNotIn("NL", infer(formula, "linear"), formula)
            self.assertNotIn("NL", infer(formula, "skip"), formula)
            script, _ = parse_str(formula)
            self.assertTrue(divides_by_zero(script), formula)
        for formula in [
            INT_XY + "(assert (= (div x 3) y))",
            INT_XY + "(assert (= (div 0 x) y))",
            REAL_R + "(assert (= (/ r 10.0) r))",
        ]:
            script, _ = parse_str(formula)
            self.assertFalse(divides_by_zero(script), formula)

        seed, _ = parse_str("(set-logic QF_LIA)" + INT_XY +
                            "(assert (= (div x 3) y))")
        mutant, _ = parse_str(INT_XY + "(assert (= (mod x 0) y))")
        fuzzer = make_fuzzer("widen")
        fuzzer.init_logic([seed])
        self.assertEqual(fuzzer.mutant_logic(mutant), ("QF_NIA", True))
        fuzzer = make_fuzzer("skip")
        fuzzer.init_logic([seed])
        self.assertEqual(fuzzer.mutant_logic(mutant), (None, False))
        for mode in ["linear", "skip"]:
            fuzzer = make_fuzzer("widen", mode)
            fuzzer.init_logic([seed])
            self.assertEqual(fuzzer.mutant_logic(mutant), ("QF_LIA", True))

    def test_ground_divisors(self):
        # Checked with z3 5.3.3 and cvc5 1.4.2 in QF_LIA and QF_LRA.
        # z3 accepts only numerals, decimals, unary - and / over them as
        # divisors and factors; (- 5 2) is rejected as non-linear.
        for formula in [
            INT_XY + "(assert (= (div x (- 5 2)) y))",
            INT_XY + "(assert (= (* x (- 5 2)) y))",
            INT_XY + "(assert (= (div 7 (+ 1 1)) y))",
            REAL_R + "(assert (= (/ r (- 5.0 2.0)) r))",
            REAL_R + "(assert (= (/ 6.0 (* 2.0 3.0)) r))",
            REAL_R + "(assert (= (* (/ (/ 1.0 2.0) 3.0) r) r))",
            REAL_R + "(assert (= (/ r (/ 1.0 2.0 3.0)) r))",
            REAL_R + "(assert (= (/ r (/ (- (- 1.0)) 2.0)) r))",
            REAL_R + "(assert (= (/ 1133.0 (/ 1133.0 (/ 1133.0 100.0))) r))",
            INT_XY + "(assert (= (* (div 4 2) x) y))",
            INT_XY + "(assert (let ((c (- 5 2))) (= (* c x) y)))",
        ]:
            for mode in DIV_BY_ZERO_MODES:
                self.assertIn("NL", infer(formula, mode), formula)
            script, _ = parse_str(formula)
            self.assertFalse(divides_by_zero(script), formula)
        # Both accept these in linear logics.
        for formula in [
            INT_XY + "(assert (= (div x (- 5)) y))",
            REAL_R + "(assert (= (/ r (/ 4.0 2.0)) r))",
            REAL_R + "(assert (= (/ (* 100.0 1133.0) 100.0) r))",
            REAL_R + "(assert (= (* (- (/ 1.0 2.0)) r) r))",
            REAL_R + "(assert (= (/ r (/ (- 1.0) (- 2.0))) r))",
            REAL_R + "(assert (= (* (- (- 1.0)) r) r))",
        ]:
            self.assertNotIn("NL", infer(formula), formula)
        # Divisors that evaluate to zero: cvc5 rejects them in linear
        # logics, also when they are not literals (E5: (- 5000000 5000000)
        # from typefuzz).
        for formula in [
            REAL_R + "(assert (= (/ 1.0 (- 5000000.0 5000000.0)) r))",
            INT_XY + "(assert (= (mod x (- 2 2)) y))",
            INT_XY + "(assert (= (div x (* 3 (- 2 2))) y))",
            REAL_R + "(assert (= (/ r (/ 0.0 2.0)) r))",
            INT_XY + "(assert (let ((c (- 3 3))) (= (div x c) y)))",
        ]:
            self.assertIn("NL", infer(formula), formula)
            script, _ = parse_str(formula)
            self.assertTrue(divides_by_zero(script), formula)
        # Values that are too large are not computed.
        big = "(* " + " ".join(["1000000000000"] * 400) + ")"
        script, _ = parse_str(
            INT_XY + "(assert (= (div x (- %s %s)) y))" % (big, big))
        self.assertFalse(divides_by_zero(script))

    def test_seed_logic(self):
        def seed(logic, body=INT_XY):
            script, _ = parse_str("(set-logic " + logic + ")" + body)
            return script

        fuzzer = make_fuzzer("widen")
        # Difference logics are run as LIA/LRA.
        fuzzer.init_logic([seed("QF_IDL")])
        self.assertEqual(fuzzer.seed_logic, "QF_LIA")
        # Fusion of seeds with different logics uses their union.
        fuzzer.init_logic([seed("QF_LIA"), seed("QF_LRA", REAL_R)])
        self.assertEqual(fuzzer.seed_logic, "QF_LIRA")
        # Unknown logics are kept if the seeds agree, ALL otherwise.
        fuzzer.init_logic([seed("ALL"), seed("ALL")])
        self.assertEqual(fuzzer.seed_logic, "ALL")
        fuzzer.init_logic([seed("ALL"), seed("QF_LIA")])
        self.assertEqual(fuzzer.seed_logic, "ALL")
        # No set-logic if a seed has none.
        no_logic, _ = parse_str(INT_XY)
        fuzzer.init_logic([seed("QF_LIA"), no_logic])
        self.assertIsNone(fuzzer.seed_logic)


if __name__ == "__main__":
    unittest.main()
