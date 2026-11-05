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

"""
Parsing, typechecking and printing of the SMT-LIB theories beyond core and
arithmetic: bit-vectors, floating point, arrays, uninterpreted functions,
datatypes and annotated terms.
"""

import sys
import unittest

sys.path.append("../../")

from yinyang.src.parsing.Ast import Assert  # noqa: E402
from yinyang.src.parsing.Parse import parse_str  # noqa: E402
from yinyang.src.parsing.Typechecker import (  # noqa: E402
    typecheck, TypeCheckError,
)
from yinyang.src.parsing.Types import (  # noqa: E402
    sort2type, ARRAY_TYPE, BITVECTOR_TYPE, FP_TYPE, FUNCTION_TYPE,
    BOOLEAN_TYPE, INTEGER_TYPE, REAL_TYPE, ROUNDINGMODE_TYPE, UNKNOWN,
)


def parse(formula):
    script, glob = parse_str(formula, silent=False)
    if script is None:
        raise AssertionError("parse error:\n" + formula)
    return script, glob


def assert_types(formula):
    """Parse and typecheck formula, return the types of its asserts."""
    script, glob = parse(formula)
    typecheck(script, glob)
    return [cmd.term.type for cmd in script.commands
            if isinstance(cmd, Assert)]


def assert_terms(formula):
    """Parse and typecheck formula, return the terms of its asserts."""
    script, glob = parse(formula)
    typecheck(script, glob)
    return [cmd.term for cmd in script.commands if isinstance(cmd, Assert)]


def ill_typed(formula):
    script, glob = parse(formula)
    try:
        typecheck(script, glob)
    except TypeCheckError:
        return True
    return False


BV8 = BITVECTOR_TYPE(8)
BV_XY = "(declare-fun x () (_ BitVec 8))(declare-fun y () (_ BitVec 8))"


class TheoriesTestCase(unittest.TestCase):
    def test_types(self):
        # Types compare and hash by value, so that they can be used as
        # dictionary keys and compared with ==.
        self.assertEqual(sort2type("(_ BitVec 8)"), BV8)
        self.assertEqual(hash(sort2type("(_ BitVec 8)")), hash(BV8))
        self.assertNotEqual(BV8, BITVECTOR_TYPE(4))
        self.assertNotEqual(BV8, INTEGER_TYPE)
        self.assertEqual(sort2type("Float32"), FP_TYPE(8, 24))
        self.assertEqual(sort2type("Float16"), FP_TYPE(5, 11))
        self.assertEqual(sort2type("Float64"), FP_TYPE(11, 53))
        self.assertEqual(sort2type("Float128"), FP_TYPE(15, 113))
        nested = sort2type("(Array (_ BitVec 4) (Array Int (_ BitVec 8)))")
        self.assertEqual(
            nested,
            ARRAY_TYPE(BITVECTOR_TYPE(4), ARRAY_TYPE(INTEGER_TYPE, BV8)))
        self.assertEqual(
            str(nested), "(Array (_ BitVec 4) (Array Int (_ BitVec 8)))")
        self.assertEqual(len({nested, sort2type(str(nested))}), 1)
        self.assertEqual(sort2type("U"), "U")
        self.assertEqual(sort2type("(Seq Int)"), "(Seq Int)")

    def test_bv_literals(self):
        # A1: #x and #b literals are bit-vectors of width 4n and n.
        terms = assert_terms(BV_XY + "(assert (= (bvadd x y) #x01))"
                             "(assert (= ((_ extract 2 0) x) #b101))")
        self.assertEqual(terms[0].subterms[1].type, BV8)
        self.assertEqual(terms[1].subterms[1].type, BITVECTOR_TYPE(3))
        self.assertEqual(
            assert_types("(declare-fun |a&b| () (_ BitVec 4))"
                         "(assert (= |a&b| #x0))"), [BOOLEAN_TYPE])
        self.assertTrue(ill_typed(BV_XY + "(assert (= x #x1))"))
        self.assertTrue(ill_typed(BV_XY + "(assert (= x 1))"))

    def test_uf(self):
        # A2: applications of declared and defined functions.
        terms = assert_terms(
            "(declare-fun f (Int Bool) Real)"
            "(define-fun g ((a Int) (b Int)) Int (+ a b))"
            "(define-fun c () Int 3)"
            "(assert (= (f 1 true) 2.0))"
            "(assert (= (g 1 c) 2))")
        self.assertEqual(terms[0].subterms[0].type, REAL_TYPE)
        self.assertEqual(terms[1].subterms[0].type, INTEGER_TYPE)
        self.assertEqual(terms[1].subterms[0].subterms[1].type, INTEGER_TYPE)
        self.assertTrue(ill_typed(
            "(declare-fun f (Int) Int)(assert (= (f true) 1))"))
        self.assertTrue(ill_typed(
            "(declare-fun f (Int) Int)(assert (= (f 1 2) 1))"))

    def test_annotations(self):
        # A3: annotated terms parse, typecheck and print unchanged.
        formula = (
            "(declare-fun f (Int) Int)\n"
            "(declare-fun p () Bool)\n"
            "(assert (! p :named a1))\n"
            "(assert (forall ((x Int)) (! (> (f x) 0) :pattern ((f x)) "
            ":qid q1)))\n"
            "(check-sat)")
        script, glob = parse(formula)
        typecheck(script, glob)
        self.assertEqual(script.__str__(), formula)
        self.assertEqual(script.commands[2].term.type, BOOLEAN_TYPE)
        self.assertEqual(script.commands[3].term.type, BOOLEAN_TYPE)

    def test_function_signatures(self):
        # A4: function signatures with indexed and parametric sorts.
        script, glob = parse(
            "(declare-fun f (Bool (_ BitVec 4) (Array Int Int))"
            " (_ BitVec 8))(assert (= (f true #x0 a) #x00))")
        self.assertEqual(
            glob["f"],
            FUNCTION_TYPE([BOOLEAN_TYPE, BITVECTOR_TYPE(4),
                           ARRAY_TYPE(INTEGER_TYPE, INTEGER_TYPE)], BV8))
        self.assertEqual(
            script.commands[0].__str__(),
            "(declare-fun f (Bool (_ BitVec 4) (Array Int Int))"
            " (_ BitVec 8))")
        self.assertEqual(
            assert_types("(declare-fun a () (Array Int Int))"
                         "(declare-fun f (Bool (_ BitVec 4) (Array Int Int))"
                         " (_ BitVec 8))(assert (= (f true #x0 a) #x00))"),
            [BOOLEAN_TYPE])

    def test_bv_ops(self):
        # A5: all operators of FixedSizeBitVectors and QF_BV.
        for op in ["bvand", "bvor", "bvxor", "bvnand", "bvnor", "bvxnor",
                   "bvadd", "bvsub", "bvmul", "bvudiv", "bvurem", "bvsdiv",
                   "bvsrem", "bvsmod", "bvshl", "bvlshr", "bvashr"]:
            terms = assert_terms(BV_XY + "(assert (= (%s x y) x))" % op)
            self.assertEqual(terms[0].subterms[0].type, BV8, op)
        for op in ["bvult", "bvule", "bvugt", "bvuge",
                   "bvslt", "bvsle", "bvsgt", "bvsge"]:
            self.assertEqual(
                assert_types(BV_XY + "(assert (%s x y))" % op),
                [BOOLEAN_TYPE], op)
            self.assertTrue(ill_typed(
                BV_XY + "(assert (%s x #x1))" % op), op)
        cases = [
            ("(bvnot x)", 8), ("(bvneg x)", 8), ("(bvcomp x y)", 1),
            ("(concat x #x1)", 12), ("((_ extract 7 4) x)", 4),
            ("((_ zero_extend 8) x)", 16), ("((_ sign_extend 0) x)", 8),
            ("((_ repeat 3) x)", 24), ("((_ rotate_left 1) x)", 8),
            ("((_ rotate_right 9) x)", 8), ("(_ bv5 3)", 3),
        ]
        for term, width in cases:
            terms = assert_terms(BV_XY + "(assert (= %s %s))" % (term, term))
            self.assertEqual(
                terms[0].subterms[0].type, BITVECTOR_TYPE(width), term)
        self.assertTrue(ill_typed(BV_XY + "(assert (= (bvadd x #x1) x))"))
        self.assertTrue(ill_typed(BV_XY + "(assert (= (concat x y) x))"))

    def test_fp(self):
        # A6: FP sort aliases, literals, rounding modes and operators.
        fp32 = FP_TYPE(8, 24)
        terms = assert_terms(
            "(declare-fun x () Float32)(declare-fun r () Real)"
            "(declare-fun m () RoundingMode)"
            "(assert (fp.isNaN x))"
            "(assert (fp.eq x (fp #b0 #b01111111 #b00000000000000000000000)))"
            "(assert (fp.isZero ((_ to_fp 8 24) RNE r)))"
            "(assert (= (fp.sqrt roundTowardZero x) (fp.rem x x)))"
            "(assert (= (fp.fma m x x x) (fp.roundToIntegral RTP x)))"
            "(assert (= (fp.min x x) (_ +zero 8 24) (_ -oo 8 24)"
            " (_ NaN 8 24)))"
            "(assert (= ((_ fp.to_ubv 4) RNA x) ((_ fp.to_sbv 4) RTN x)))"
            "(assert (= (fp.to_real x) r))"
            "(assert (= ((_ to_fp 11 53) RNE x) ((_ to_fp 11 53) #x0000000000000000)))")  # noqa: E501
        self.assertEqual(terms[1].subterms[1].type, fp32)
        self.assertEqual(terms[2].subterms[0].subterms[0].type,
                         ROUNDINGMODE_TYPE)
        self.assertEqual(terms[3].subterms[0].type, fp32)
        self.assertEqual(terms[4].subterms[1].type, fp32)
        self.assertEqual(terms[5].subterms[3].type, fp32)
        self.assertEqual(terms[6].subterms[0].type, BITVECTOR_TYPE(4))
        self.assertEqual(terms[7].subterms[0].type, REAL_TYPE)
        self.assertEqual(terms[8].subterms[0].type, FP_TYPE(11, 53))
        self.assertTrue(ill_typed(
            "(declare-fun x () Float32)(declare-fun y () Float64)"
            "(assert (fp.eq x y))"))
        self.assertTrue(ill_typed(
            "(declare-fun x () Float32)(assert (fp.isNaN (fp.add x x x)))"))

    def test_arrays(self):
        # A7: select and store compare index and element types by value.
        terms = assert_terms(
            "(declare-fun a () (Array (_ BitVec 8) (_ BitVec 32)))"
            "(declare-fun b () (Array (_ BitVec 32) (_ BitVec 8)))"
            "(declare-fun c () (Array Int (Array Int Bool)))"
            "(assert (= (select a #x00) #x00000000))"
            "(assert (= (store b (_ bv0 32) #x00) b))"
            "(assert (select (select c 0) 1))"
            "(assert (= ((as const (Array Int Int)) 0) (store "
            "((as const (Array Int Int)) 1) 0 0)))")
        self.assertEqual(terms[0].subterms[0].type, BITVECTOR_TYPE(32))
        self.assertEqual(terms[1].subterms[0].type,
                         ARRAY_TYPE(BITVECTOR_TYPE(32), BV8))
        self.assertEqual(terms[2].type, BOOLEAN_TYPE)
        self.assertEqual(terms[3].subterms[0].type,
                         ARRAY_TYPE(INTEGER_TYPE, INTEGER_TYPE))
        self.assertTrue(ill_typed(
            "(declare-fun a () (Array (_ BitVec 8) Int))"
            "(assert (= (select a #x0) 0))"))
        self.assertTrue(ill_typed(
            "(declare-fun a () (Array Int (_ BitVec 8)))"
            "(assert (= (store a 0 #x0) a))"))

    def test_datatypes(self):
        # A8: constructors, selectors and testers of declared datatypes.
        dt = ("(declare-datatypes ((L 0) (P 0)) (((nil) (cons (hd Int) "
              "(tl L))) ((pair (fst L) (snd Bool)))))"
              "(declare-datatype C ((red) (green)))"
              "(declare-fun l () L)")
        terms = assert_terms(
            dt + "(assert ((_ is cons) l))"
            "(assert (= (hd l) 1))"
            "(assert (= (tl (cons 1 nil)) l))"
            "(assert (snd (pair l true)))"
            "(assert (distinct red green))"
            "(assert (is-nil l))")
        self.assertEqual([t.type for t in terms], [BOOLEAN_TYPE] * 6)
        self.assertEqual(terms[1].subterms[0].type, INTEGER_TYPE)
        self.assertEqual(terms[2].subterms[0].type, "L")
        self.assertEqual(terms[4].subterms[0].type, "C")
        self.assertTrue(terms[4].subterms[0].is_const)
        # Parametric datatypes are not supported, but do not break parsing.
        script, _ = parse(
            "(declare-datatypes ((Opt 1)) ((par (T) ((none) (some (val T))))))"
            "(declare-fun o () (Opt Int))(assert (= o o))")
        self.assertEqual(script.global_vars["o"], "(Opt Int)")
        self.assertTrue(ill_typed(dt + "(assert (= (hd l) true))"))
        self.assertTrue(ill_typed(dt + "(assert ((_ is cons) 1))"))

    def test_error_messages(self):
        # A9: type errors involving non-string types are reported as
        # TypeCheckError, not as a TypeError raised while printing them.
        script, glob = parse(BV_XY + "(assert (= (bvadd x #x1) x))")
        with self.assertRaises(TypeCheckError) as cm:
            typecheck(script, glob)
        self.assertIn("expected: \t(_ BitVec 8)", str(cm.exception))
        self.assertIn("actual: \t(_ BitVec 4)", str(cm.exception))
        var = script.commands[2].term.subterms[0].subterms[0]
        self.assertEqual(repr(var), "x:(_ BitVec 8)")

    def test_arithmetic(self):
        # A10: mixed Int/Real arithmetic is Real, whatever the order.
        terms = assert_terms(
            "(declare-fun x () Real)(declare-fun i () Int)"
            "(assert (= (* (- 1) x) (+ 0 x) (- i x) (+ 1 2 x)))"
            "(assert (= (+ i 1) (* 2 i) (- i)))")
        self.assertEqual([t.type for t in terms[0].subterms],
                         [REAL_TYPE] * 4)
        self.assertEqual([t.type for t in terms[1].subterms],
                         [INTEGER_TYPE] * 3)

    def test_strings(self):
        # Indexed string operators, and str.to_code.
        terms = assert_terms(
            "(declare-fun s () String)"
            "(assert (str.in_re s ((_ re.loop 1 3) (str.to_re \"a\"))))"
            "(assert (str.in_re s ((_ re.^ 2) re.allchar)))"
            "(assert (= (str.to_code s) 65))")
        self.assertEqual([t.type for t in terms], [BOOLEAN_TYPE] * 3)

    def test_printing(self):
        # A11: declarations with Array/BV/FP sorts print as SMT-LIB.
        formula = (
            "(declare-const tbl (Array (_ BitVec 32) (_ BitVec 8)))\n"
            "(declare-const f (_ FloatingPoint 8 24))\n"
            "(declare-const g Float64)\n"
            "(declare-fun h ((Array Int Int) (_ BitVec 4)) Bool)\n"
            "(assert (h ((as const (Array Int Int)) 0) #x0))\n"
            "(check-sat)")
        script, glob = parse(formula)
        typecheck(script, glob)
        # Sort aliases are printed in their canonical form.
        self.assertEqual(
            script.__str__(),
            formula.replace("Float64", "(_ FloatingPoint 11 53)"))

    def test_no_unknown_types(self):
        script, glob = parse(
            "(declare-fun f ((_ BitVec 8)) (_ BitVec 8))" + BV_XY +
            "(assert (bvsle (f x) (bvadd y #x01)))")
        typecheck(script, glob)

        def walk(t):
            self.assertNotEqual(t.type, UNKNOWN, t.__str__())
            for s in t.subterms or []:
                walk(s)
        walk(script.commands[3].term)


if __name__ == "__main__":
    unittest.main()
