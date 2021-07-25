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

sys.setrecursionlimit(100000)

from src.parsing.Types import (
    sort2type,
    # Types
    BOOLEAN_TYPE, REAL_TYPE, INTEGER_TYPE, ROUNDINGMODE_TYPE, STRING_TYPE,
    REGEXP_TYPE, UNKNOWN, ARRAY_TYPE, BITVECTOR_TYPE, FP_TYPE,
    # Operator lists
    CORE_OPS, NUMERICAL_OPS, REAL_OPS, INT_OPS, REAL_INTS, STRING_OPS,
    ARRAY_OPS, BV_OPS, FP_OPS,
    # Operators
    NOT, AND, OR, XOR, IMPLIES, ITE, EQ, UNARY_MINUS, MINUS, PLUS, MULTIPLY,
    GT, GTE, LT, LTE, DIV, MOD, ABS, REAL_DIV, TO_REAL, TO_INT, IS_INT,
    CONCAT, STRLEN, LEXORD, REFLEX_CLOS, STR_PREFIXOF, STR_SUFFIXOF,
    STR_CONTAINS, RE_NONE, RE_ALL, RE_ALLCHAR, STR_IN_RE, RE_COMP, RE_KLENE,
    RE_OPT, RE_PLUS, RE_DIFF, RE_CONCAT, RE_UNION, RE_INTER, STR_AT,
    STR_SUBSTR, STR_INDEXOF, STR_REPLACE, STR_REPLACE_ALL, STR_REPLACE_RE,
    STR_REPLACE_RE_ALL, STR_TO_CODE, STR_TO_INT, STR_TO_RE, STR_FROM_CODE,
    STR_FROM_INT, STR_IS_DIGIT, RE_RANGE, SELECT, STORE, BV_CONCAT, BVNOT,
    BVNEG, BVAND, BVOR, BVXOR, BVADD, BVSUB, BVMUL, BVUDIV, BVUREM, BVSHL,
    BV_EXTRACT, BV_ZERO_EXTEND, BV_SIGN_EXTEND, BVLSHR, BVASHR, BVSDIV, BVULT,
    BVULE, BVSLT, BVSGT, FP_ABS, FP_NEG, FP_ADD, FP_SUB, FP_MUL, FP_DIV,
    FP_SQRT, FP_REM, FP_ROUND_TO_INTEGRAL, FP_NORMAL, FP_ISSUBNORMAL,
    FP_IS_ZERO, FP_ISINFINITE, FP_ISNAN, FP_ISNEGATIVE, FP_ISPOSITIVE, FP_LEQ,
    FP_LT, FP_GEQ, FP_GT, FP_EQ, FP_MIN, FP_MAX, FP_FMA, TO_FP_UNSIGNED, TO_FP
)

from src.parsing.Ast import Assert


class Context:
    def __init__(self, globals, locals):
        self.globals = globals
        self.locals = locals

    def add_to_globals(self, var, type):
        if isinstance(type, str):
            self.globals[var] = sort2type(type)
        else:
            self.globals[var] = type

    def add_to_locals(self, var, type):
        if isinstance(type, str):
            self.locals[var] = sort2type(type)
        else:
            self.locals[var] = type


class TypeCheckError(Exception):
    def __init__(self, expr, subterm=None, expected=None, actual=None):
        self.message = "Ill-typed expression \nterm: \t \t"\
                       + expr.__str__() + "\n"
        if isinstance(subterm, list):
            s = "[" + subterm[0].__str__() + " "
            for term in subterm[1:]:
                s += term.__str__() + " "
            s += "]"
            self.message += "faulty subterm:\t" + subterm.__str__() + "\n"
        else:
            self.message += "faulty subterm:\t" + subterm.__str__() + "\n"
        self.message += "expected: \t" + str(expected) + "\n"
        self.message += "actual: \t" + str(actual)
        super().__init__(self.message)


class UnknownOperator(Exception):
    def __init__(self, op):
        self.message = "unknown function/constant " + op
        # sys.tracebacklimit = 0
        super().__init__(self.message)


def typecheck_not(expr, ctxt=[]):
    """(not Bool Bool)"""
    typ = typecheck_expr(expr.subterms[0], ctxt)
    if typ != BOOLEAN_TYPE:
        raise TypeCheckError(expr, expr.subterms[0], typ, BOOLEAN_TYPE)
    return BOOLEAN_TYPE


def typecheck_unary_minus(expr, ctxt=[]):
    """(- Int Int)
    (- Real Real)
    """
    typ = typecheck_expr(expr.subterms[0], ctxt)
    if typ not in [INTEGER_TYPE, REAL_TYPE]:
        raise TypeCheckError(
            expr, expr.subterms[0], [INTEGER_TYPE, REAL_TYPE], typ
        )
    return typecheck_expr(expr.subterms[0], ctxt)


def typecheck_nary_numeral_ret(expr, ctxt=[]):
    """(- Int Int Int :left-assoc)
    (+ Int Int Int :left-assoc)
    (* Int Int Int :left-assoc)
    (- Real Real Real :left-assoc)
    (+ Real Real Real :left-assoc)
    (* Real Real Real :left-assoc)
    (/ Real Real Real :left-assoc)
    """
    typ = typecheck_expr(expr.subterms[0], ctxt)
    if typ not in [INTEGER_TYPE, REAL_TYPE]:
        raise TypeCheckError(
            expr, expr.subterms[0], [INTEGER_TYPE, REAL_TYPE], typ
        )
    for term in expr.subterms[1:]:
        t = typecheck_expr(term, ctxt)
        if t not in [INTEGER_TYPE, REAL_TYPE]:
            raise TypeCheckError(expr, term, typ, t)
    return typ


def typecheck_nary_int_ret(expr, ctxt=[]):
    """(div Int Int Int :left-assoc)
    (mod Int Int Int)
    (abs Int Int)
    """
    for term in expr.subterms:
        t = typecheck_expr(term, ctxt)
        if t != INTEGER_TYPE:
            raise TypeCheckError(expr, term, INTEGER_TYPE, t)
    return INTEGER_TYPE


def is_subtype(t, tprime):
    if t == INTEGER_TYPE and tprime == REAL_TYPE:
        return True
    if isinstance(t, BITVECTOR_TYPE) and isinstance(tprime, BITVECTOR_TYPE):
        return True
    return False


def typecheck_eq(expr, ctxt=[]):
    """(par (A) (= A A Bool :chainable))
    (par (A) (distinct A A Bool :pairwise))
    """
    typ = typecheck_expr(expr.subterms[0], ctxt)
    for term in expr.subterms[1:]:
        t = typecheck_expr(term, ctxt)
        if t != typ:
            if not (is_subtype(t, typ) or is_subtype(typ, t)):
                raise TypeCheckError(expr, term, typ, t)
    return BOOLEAN_TYPE


def typecheck_ite(expr, ctxt=[]):
    """(par (A) (ite Bool A A A))"""
    typ = typecheck_expr(expr.subterms[0], ctxt)
    if typecheck_expr(expr.subterms[0], ctxt) != BOOLEAN_TYPE:
        t = typecheck_expr(expr.subterms[1], ctxt)
        if not (is_subtype(t, typ) or is_subtype(typ, t)):
            raise TypeCheckError(expr, expr.subterms[0], typ, BOOLEAN_TYPE)
    t1 = typecheck_expr(expr.subterms[1], ctxt)
    t2 = typecheck_expr(expr.subterms[2], ctxt)
    if t1 != t2:
        if not (is_subtype(t1, t2) or is_subtype(t2, t1)):
            raise TypeCheckError(expr, expr.subterms[2], t1, t2)
    return typecheck_expr(expr.subterms[1], ctxt)


def typecheck_nary_bool(expr, ctxt=[]):
    """
    (and Bool Bool Bool :left-assoc)
    (or Bool Bool Bool :left-assoc)
    (xor Bool Bool Bool :left-assoc)
    """
    for term in expr.subterms:
        typ = typecheck_expr(term, ctxt)
        if typ != BOOLEAN_TYPE:
            raise TypeCheckError(expr, term, BOOLEAN_TYPE, typ)
    return BOOLEAN_TYPE


def typecheck_comp_ops(expr, ctxt):
    """
    (<= Int Int Bool :chainable)
    (<  Int Int Bool :chainable)
    (>= Int Int Bool :chainable)
    (>  Int Int Bool :chainable)
    (<= Real Real Bool :chainable)
    (<  Real Real Bool :chainable)
    (>= Real Real Bool :chainable)
    (>  Real Real Bool :chainable)
    """
    typ = typecheck_expr(expr.subterms[0], ctxt)
    if typ not in [INTEGER_TYPE, REAL_TYPE]:
        raise TypeCheckError(
            expr, expr.subterms[0], [INTEGER_TYPE, REAL_TYPE], typ
        )

    for term in expr.subterms[1:]:
        t = typecheck_expr(term, ctxt)
        if t not in [INTEGER_TYPE, REAL_TYPE]:
            raise TypeCheckError(expr, term, [INTEGER_TYPE, REAL_TYPE], t)
    return BOOLEAN_TYPE


def typecheck_to_real(expr, ctxt):
    """(to_real Int Real)"""
    t = typecheck_expr(expr, ctxt)
    if t != INTEGER_TYPE:
        raise TypeCheckError(expr, expr, INTEGER_TYPE, t)
    return REAL_TYPE


def typecheck_to_int(expr, ctxt):
    """(to_int Real Int)"""
    t = typecheck_expr(expr, ctxt)
    if t != REAL_TYPE or t != INTEGER_TYPE:
        raise TypeCheckError(expr, expr, REAL_TYPE, t)
    return INTEGER_TYPE


def typecheck_is_int(expr, ctxt):
    """(is_int Real Bool)"""
    t = typecheck_expr(expr, ctxt)
    if t != REAL_TYPE or t != INTEGER_TYPE:
        raise TypeCheckError(expr, expr, REAL_TYPE, t)
    return BOOLEAN_TYPE


def typecheck_real_div(expr, ctxt):
    """(/ Real Real Real :left-assoc)"""
    for term in expr.subterms:
        t = typecheck_expr(term, ctxt)
        if t not in [REAL_TYPE, INTEGER_TYPE]:
            raise TypeCheckError(expr, expr, REAL_TYPE, t)
    return REAL_TYPE


def typecheck_string_concat(expr, ctxt):
    """(str.++ String String String :left-assoc)"""
    for term in expr.subterms:
        t = typecheck_expr(term, ctxt)
        if t != STRING_TYPE:
            raise TypeCheckError(expr, expr, STRING_TYPE, t)
    return STRING_TYPE


def typecheck_strlen(expr, ctxt):
    """(str.len String Int)"""
    t = typecheck_expr(expr.subterms[0], ctxt)
    if t != STRING_TYPE:
        raise TypeCheckError(expr, expr, STRING_TYPE, t)
    return INTEGER_TYPE


def typecheck_nary_string_rt_bool(expr, ctxt):
    """(str.< String String Bool :chainable)
    (str.<= String String Bool :chainable)
    (str.prefixof String String Bool)
    (str.suffixof String String Bool)
    (str.contains String String Bool)
    """
    for term in expr.subterms:
        t = typecheck_expr(term, ctxt)
        if t != STRING_TYPE:
            raise TypeCheckError(expr, expr, STRING_TYPE, t)
    return BOOLEAN_TYPE


def typecheck_str_to_re(expr, ctxt):
    """(str.to_re String RegLan)"""
    arg = expr.subterms[0]
    t = typecheck_expr(arg, ctxt)
    if t != STRING_TYPE:
        raise TypeCheckError(expr, expr, STRING_TYPE, t)
    return REGEXP_TYPE


def typecheck_regex_consts(expr, ctxt):
    """
    (re.none RegLan)
    (re.all RegLan)
    (re.allchar RegLan)
    """
    return REGEXP_TYPE


def typecheck_str_in_re(expr, ctxt):
    """(str.in_re String RegLan Bool)"""
    s = typecheck_expr(expr.subterms[0], ctxt)
    t = typecheck_expr(expr.subterms[1], ctxt)

    if s != STRING_TYPE:
        raise TypeCheckError(expr, expr, STRING_TYPE, t)

    if t != REGEXP_TYPE:
        raise TypeCheckError(expr, expr, REGEXP_TYPE, t)
    return BOOLEAN_TYPE


def typecheck_regex_unary(expr, ctxt):
    """
    (re.* RegLan RegLan)
    (re.comp RegLan RegLan)
    (re.opt RegLan RegLan)
    (re.+ RegLan RegLan)
    """
    t = typecheck_expr(expr, ctxt)
    if t != REGEXP_TYPE:
        raise TypeCheckError(expr, expr, REGEXP_TYPE, t)
    return REGEXP_TYPE


def typecheck_regex_binary(expr, ctxt):
    """
    (re.diff RegLan RegLan RegLan :left-assoc)
    (re.++ RegLan RegLan RegLan :left-assoc)
    (re.union RegLan RegLan RegLan :left-assoc)
    (re.inter RegLan RegLan RegLan :left-assoc)
    """
    for term in expr.subterms:
        t = typecheck_expr(term, ctxt)
        if t != REGEXP_TYPE:
            raise TypeCheckError(expr, term, REGEXP_TYPE, t)
    return REGEXP_TYPE


def typecheck_str_at(expr, ctxt):
    """
    (str.at String Int String)
    """
    t1 = typecheck_expr(expr.subterms[0], ctxt)
    t2 = typecheck_expr(expr.subterms[1], ctxt)
    if t1 != STRING_TYPE:
        raise TypeCheckError(expr, expr, STRING_TYPE, t1)
    if t2 != INTEGER_TYPE:
        raise TypeCheckError(expr, expr, INTEGER_TYPE, t2)
    return STRING_TYPE


def typecheck_substr(expr, ctxt):
    """
    (str.substr String Int Int String)
    """
    t1 = typecheck_expr(expr.subterms[0], ctxt)
    t2 = typecheck_expr(expr.subterms[1], ctxt)
    t3 = typecheck_expr(expr.subterms[2], ctxt)
    if t1 != STRING_TYPE or t2 != INTEGER_TYPE or t3 != INTEGER_TYPE:
        raise TypeCheckError(
            expr, expr, [STRING_TYPE, INTEGER_TYPE, INTEGER_TYPE], [t1, t2, t3]
        )
    return STRING_TYPE


def typecheck_index_of(expr, ctxt):
    """(str.indexof String String Int Int)"""
    t1 = typecheck_expr(expr.subterms[0], ctxt)
    t2 = typecheck_expr(expr.subterms[1], ctxt)
    t3 = typecheck_expr(expr.subterms[2], ctxt)
    if t1 != STRING_TYPE or t2 != STRING_TYPE or t3 != INTEGER_TYPE:
        raise TypeCheckError(
            expr, expr, [STRING_TYPE, STRING_TYPE, INTEGER_TYPE], [t1, t2, t3]
        )
    return INTEGER_TYPE


def typecheck_replace(expr, ctxt):
    """
    (str.replace String String String String)
    (str.replace_all String String String String)
    """
    t1 = typecheck_expr(expr.subterms[0], ctxt)
    t2 = typecheck_expr(expr.subterms[1], ctxt)
    t3 = typecheck_expr(expr.subterms[2], ctxt)
    if t1 != STRING_TYPE or t2 != STRING_TYPE or t3 != STRING_TYPE:
        raise TypeCheckError(
            expr, expr, [STRING_TYPE, STRING_TYPE, STRING_TYPE], [t1, t2, t3]
        )
    return STRING_TYPE


def typecheck_replace_re(expr, ctxt):
    """
    (str.replace_re String RegLan String String)
    (str.replace_re_all String RegLan String String)
    """
    t1 = typecheck_expr(expr.subterms[0], ctxt)
    t2 = typecheck_expr(expr.subterms[1], ctxt)
    t3 = typecheck_expr(expr.subterms[2], ctxt)
    if (
        typecheck_expr(expr.subterms[0], ctxt) != STRING_TYPE
        or typecheck_expr(expr.subterms[1], ctxt) != REGEXP_TYPE
        or typecheck_expr(expr.subterms[2], ctxt) != STRING_TYPE
    ):
        raise TypeCheckError(
            expr, expr, [STRING_TYPE, STRING_TYPE, STRING_TYPE], [t1, t2, t3]
        )
    return STRING_TYPE


def typecheck_re_range(expr, ctxt):
    """
    (re.range String String RegLan)
    """
    t1 = typecheck_expr(expr.subterms[0], ctxt)
    t2 = typecheck_expr(expr.subterms[1], ctxt)

    if t1 != STRING_TYPE or t2 != STRING_TYPE:
        raise TypeCheckError(expr, expr, [STRING_TYPE, STRING_TYPE], [t1, t2])
    return REGEXP_TYPE


def typecheck_str_to_int(expr, ctxt):
    """
    (str.to_code String Int)
    (str.to_int String Int)
    """
    t = typecheck_expr(expr.subterms[0], ctxt)

    if t != STRING_TYPE:
        raise TypeCheckError(expr, expr, STRING_TYPE, t)
    return INTEGER_TYPE


def typecheck_is_digit(expr, ctxt):
    """
    (str.is_digit String Bool)
    """
    t = typecheck_expr(expr.subterms[0], ctxt)
    if t != STRING_TYPE:
        raise TypeCheckError(expr, expr, BOOLEAN_TYPE, t)
    return BOOLEAN_TYPE


def typecheck_int_to_string(expr, ctxt):
    """
    (str.from_code Int String)
    (str.from_int Int String)
    """
    t = typecheck_expr(expr.subterms[0], ctxt)
    if t != INTEGER_TYPE:
        raise TypeCheckError(expr, expr, INTEGER_TYPE, t)
    return STRING_TYPE


def typecheck_string_ops(expr, ctxt):
    if expr.op == CONCAT:
        return typecheck_string_concat(expr, ctxt)
    if expr.op == STRLEN:
        return typecheck_strlen(expr, ctxt)
    if expr.op in [
            LEXORD, REFLEX_CLOS, STR_PREFIXOF, STR_SUFFIXOF, STR_CONTAINS
    ]:
        return typecheck_nary_string_rt_bool(expr, ctxt)
    if expr.op in [RE_NONE, RE_ALL, RE_ALLCHAR]:
        return typecheck_regex_consts(expr, ctxt)
    if expr.op == STR_IN_RE:
        return typecheck_str_in_re(expr, ctxt)
    if expr.op in [RE_KLENE, RE_COMP, RE_OPT, RE_PLUS]:
        return typecheck_regex_binary(expr, ctxt)
    if expr.op in [RE_DIFF, RE_CONCAT, RE_UNION, RE_INTER]:
        return typecheck_regex_binary(expr, ctxt)
    if expr.op == STR_AT:
        return typecheck_str_at(expr, ctxt)
    if expr.op == STR_SUBSTR:
        return typecheck_substr(expr, ctxt)
    if expr.op == STR_INDEXOF:
        return typecheck_index_of(expr, ctxt)
    if expr.op in [STR_REPLACE, STR_REPLACE_ALL]:
        return typecheck_replace(expr, ctxt)
    if expr.op in [STR_REPLACE_RE, STR_REPLACE_RE_ALL]:
        return typecheck_replace(expr, ctxt)
    if expr.op in [STR_TO_CODE, STR_TO_INT]:
        return typecheck_str_to_int(expr, ctxt)
    if expr.op == STR_TO_RE:
        return typecheck_str_to_re(expr, ctxt)
    if expr.op in [STR_FROM_CODE, STR_FROM_INT]:
        return typecheck_int_to_string(expr, ctxt)
    if expr.op == STR_IS_DIGIT:
        return typecheck_is_digit(expr, ctxt)
    if expr.op == RE_RANGE:
        return typecheck_re_range(expr, ctxt)


def typecheck_select(expr, ctxt):
    """
    (select (Array X Y) X Y)
    """
    array_type = typecheck_expr(expr.subterms[0], ctxt)
    if isinstance(array_type, ARRAY_TYPE):
        raise TypeCheckError(expr, expr, ARRAY_TYPE, array_type)
    x_type = typecheck_expr(expr.subterms[1], ctxt)
    if x_type != array_type.index_type:
        raise TypeCheckError(expr, expr, array_type.index_type, x_type)
    return array_type.payload_type


def typecheck_store(expr, ctxt):
    """
    (store (Array X Y) X Y (Array X Y)))
    """
    array_type = typecheck_expr(expr.subterms[0], ctxt)
    if isinstance(array_type, ARRAY_TYPE):
        raise TypeCheckError(expr, expr, ARRAY_TYPE, array_type)
    x_type = typecheck_expr(expr.subterms[1], ctxt)
    y_type = typecheck_expr(expr.subterms[2], ctxt)
    if x_type != array_type.index_type and y_type != array_type.payload_type:
        raise TypeCheckError(
            expr,
            expr,
            [array_type.index_type, array_type.payload_type],
            [x_type, y_type],
        )
    return array_type


def typecheck_array_ops(expr, ctxt):
    if expr.op == SELECT:
        return typecheck_select(expr, ctxt)
    if expr.op == STORE:
        return typecheck_store(expr, ctxt)


def typecheck_bv_concat(expr, ctxt):
    """
    (concat (_ BitVec i) (_ BitVec j) (_ BitVec m))
    """
    arg1, arg2 = expr.subterms[0], expr.subterms[1]
    t1 = typecheck_expr(expr.subterms[0], ctxt)
    t2 = typecheck_expr(expr.subterms[1], ctxt)
    if not isinstance(t1, BITVECTOR_TYPE) or\
       not isinstance(t2, BITVECTOR_TYPE):
        raise TypeCheckError(
            expr, [arg1, arg2], [BITVECTOR_TYPE, BITVECTOR_TYPE], [t1, t2]
        )
    bitwidth = t1.bitwidth + t2.bitwidth
    return BITVECTOR_TYPE(bitwidth)


def typecheck_bv_unary(expr, ctxt):
    """
    (op1 (_ BitVec m) (_ BitVec m))
    """
    arg = expr.subterms[0]
    t = typecheck_expr(expr.subterms[0], ctxt)
    if not isinstance(t, BITVECTOR_TYPE):
        raise TypeCheckError(expr, arg, BITVECTOR_TYPE, t)
    return t


def typecheck_bv_binary(expr, ctxt):
    """
    (op2 (_ BitVec m) (_ BitVec m) (_ BitVec m))
    """
    arg1, _ = expr.subterms[0], expr.subterms[1]
    t1 = typecheck_expr(expr.subterms[0], ctxt)
    t2 = typecheck_expr(expr.subterms[1], ctxt)
    if not isinstance(t1, BITVECTOR_TYPE) or\
       not isinstance(t2, BITVECTOR_TYPE):
        expected = "[" + str(BITVECTOR_TYPE) + "," + str(BITVECTOR_TYPE) + "]"
        actual = "[" + str(t1) + "," + str(t2) + "]"
        raise TypeCheckError(expr, arg1, expected, actual)
    return BITVECTOR_TYPE(t1.bitwidth)


def typecheck_binary_bool_rt(expr, ctxt):
    """
    (bvult (_ BitVec m) (_ BitVec m) Bool)
    (bvule (_ BitVec m) (_ BitVec m) Bool)
    (bvslt (_ BitVec m) (_ BitVec m) Bool)
    """
    arg1, arg2 = expr.subterms[0], expr.subterms[1]
    t1 = typecheck_expr(expr.subterms[0], ctxt)
    t2 = typecheck_expr(expr.subterms[1], ctxt)

    if not isinstance(arg1, BITVECTOR_TYPE) or\
       not isinstance(arg2, BITVECTOR_TYPE):
        raise TypeCheckError(
            expr, [arg1, arg2], [BITVECTOR_TYPE, BITVECTOR_TYPE], [t1, t2]
        )
    return BOOLEAN_TYPE


def typecheck_bv_ops(expr, ctxt):
    if expr.op == BV_CONCAT:
        return typecheck_bv_concat(expr, ctxt)
    if expr.op in [BVNOT, BVNEG]:
        return typecheck_bv_unary(expr, ctxt)
    if expr.op in [
        BVAND,
        BVOR,
        BVXOR,
        BVADD,
        BVSUB,
        BVMUL,
        BVUDIV,
        BVUREM,
        BVSHL,
        BVLSHR,
        BVASHR,
        BVSDIV,
    ]:
        return typecheck_bv_binary(expr, ctxt)
    if expr.op in [BVULT, BVULE, BVSLT, BVSGT]:
        return typecheck_binary_bool_rt(expr, ctxt)


def typecheck_fp_unary(expr, ctxt):
    """
    (fp.abs (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
    (fp.neg (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
    """
    arg = expr.subterms[0]
    t = typecheck_expr(expr.subterms[0], ctxt)
    if not isinstance(t, FP_TYPE):
        raise TypeCheckError(expr, arg, FP_TYPE, t)
    return typecheck_expr(expr.subterms[0], ctxt)


def typecheck_fp_binary_arith(expr, ctxt):
    """
     (fp.add RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
      (_ FloatingPoint eb sb))

    (fp.sub RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
      (_ FloatingPoint eb sb))

    (fp.mul RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
      (_ FloatingPoint eb sb))

    (fp.div RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
      (_ FloatingPoint eb sb))
    """
    arg1 = expr.subterms[0]
    arg2 = expr.subterms[1]
    arg3 = expr.subterms[2]
    t1 = typecheck_expr(arg1, ctxt)
    if t1 != ROUNDINGMODE_TYPE:
        raise TypeCheckError(expr, arg1, ROUNDINGMODE_TYPE, t1)

    t1 = typecheck_expr(arg2, ctxt)
    t2 = typecheck_expr(arg3, ctxt)
    if not isinstance(t1, FP_TYPE) or not isinstance(t2, FP_TYPE):
        raise TypeCheckError(expr, [arg2, arg3], [FP_TYPE, FP_TYPE])
    return typecheck_expr(arg2, ctxt)


def typecheck_fp_unary_bool_rt(expr, ctxt):
    """
    (fp.isNormal (_ FloatingPoint eb sb) Bool)
    (fp.isSubnormal (_ FloatingPoint eb sb) Bool)
    (fp.isZero (_ FloatingPoint eb sb) Bool)
    (fp.isInfinite (_ FloatingPoint eb sb) Bool)
    (fp.isNaN (_ FloatingPoint eb sb) Bool)
    (fp.isNegative (_ FloatingPoint eb sb) Bool)
    (fp.isPositive (_ FloatingPoint eb sb) Bool)
    """
    arg = expr.subterms[0]
    typ = typecheck_expr(arg, ctxt)
    if not isinstance(typ, FP_TYPE):
        raise TypeCheckError(expr, arg, FP_TYPE, typ)
    return BOOLEAN_TYPE


def typecheck_fp_comparison(expr, ctxt):
    """
    (fp.leq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
    (fp.lt  (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
    (fp.geq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
    (fp.gt  (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
    (fp.eq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool :chainable)
    """
    arg1 = expr.subterms[0]
    arg2 = expr.subterms[1]
    typ1 = typecheck_expr(arg1, ctxt)
    typ2 = typecheck_expr(arg2, ctxt)
    if not isinstance(typ1, FP_TYPE) or not isinstance(typ2, FP_TYPE):
        args = "[" + arg1.__str__() + "," + arg2.__str__() + "]"
        expected = "[" + str(FP_TYPE) + "," + str(FP_TYPE) + "]"
        actual = "[" + typ1.__str__() + "," + typ2.__str__() + "]"
        raise TypeCheckError(expr, args, expected, actual)
    return BOOLEAN_TYPE


def typecheck_fp_minmax(expr, ctxt):
    """
    (fp.min (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)) 
    (fp.max (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
    """ # noqa E501
    arg1 = expr.subterms[0]
    arg2 = expr.subterms[1]
    if not isinstance(typecheck_expr(arg1, ctxt), FP_TYPE) or not isinstance(
        typecheck_expr(arg2, ctxt), FP_TYPE
    ):
        raise TypeCheckError(expr)
    return typecheck_expr(arg1, ctxt)


def typecheck_fp_fma(expr, ctxt):
    """
    (fp.fma RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
    """ # noqa E501
    arg1 = expr.subterms[0]
    arg2 = expr.subterms[1]
    arg3 = expr.subterms[2]
    if (
        not isinstance(typecheck_expr(arg1, ctxt), FP_TYPE)
        or not isinstance(typecheck_expr(arg2, ctxt), FP_TYPE)
        or not isinstance(typecheck_expr(arg3, ctxt), FP_TYPE)
    ):
        raise TypeCheckError(expr)
    return typecheck_expr(arg1, ctxt)


def typecheck_fp_ops(expr, ctxt):
    if expr.op in [FP_ABS, FP_NEG]:
        return typecheck_fp_unary(expr, ctxt)
    if expr.op in [
        FP_ADD,
        FP_SUB,
        FP_MUL,
        FP_DIV,
        FP_SQRT,
        FP_REM,
        FP_ROUND_TO_INTEGRAL,
    ]:
        return typecheck_fp_binary_arith(expr, ctxt)
    if expr.op in [
        FP_NORMAL,
        FP_ISSUBNORMAL,
        FP_IS_ZERO,
        FP_ISINFINITE,
        FP_ISNAN,
        FP_ISNEGATIVE,
        FP_ISPOSITIVE,
    ]:
        return typecheck_fp_unary_bool_rt(expr, ctxt)
    if expr.op in [FP_LEQ, FP_LT, FP_GEQ, FP_GT, FP_EQ]:
        return typecheck_fp_comparison(expr, ctxt)
    if expr.op in [FP_MIN, FP_MAX]:
        return typecheck_fp_minmax(expr, ctxt)
    if expr.op == FP_FMA:
        return typecheck_fp_fma(expr, ctxt)


def typecheck_quantifiers(expr, ctxt):
    vars = expr.quantified_vars[0]
    types = expr.quantified_vars[1]
    for i in range(len(vars)):
        var, type = vars[i], types[i]
        ctxt.add_to_locals(var, type)
    t = typecheck_expr(expr.subterms[0], ctxt)
    if t != BOOLEAN_TYPE:
        raise TypeCheckError(expr, expr.subterms[0], BOOLEAN_TYPE, t)
    return BOOLEAN_TYPE


def typecheck_core(expr, ctxt):
    if expr.op == NOT:
        return typecheck_not(expr, ctxt)
    if expr.op in [AND, OR, XOR, IMPLIES]:
        return typecheck_nary_bool(expr, ctxt)
    if expr.op == ITE:
        return typecheck_ite(expr, ctxt)
    if expr.op in EQ:
        return typecheck_eq(expr, ctxt)


def typecheck_numeral(expr, ctxt):
    if expr.op == UNARY_MINUS and len(expr.subterms) == 1:
        return typecheck_unary_minus(expr, ctxt)
    if expr.op in [MINUS, PLUS, MULTIPLY]:
        return typecheck_nary_numeral_ret(expr, ctxt)
    if expr.op in [GT, GTE, LT, LTE]:
        return typecheck_comp_ops(expr, ctxt)


def typecheck_int_ops(expr, ctxt):
    if expr.op in [DIV, MOD, ABS]:
        return typecheck_nary_int_ret(expr, ctxt)


def typecheck_real_ops(expr, ctxt):
    if expr.op == REAL_DIV:
        return typecheck_real_div(expr, ctxt)


def typecheck_real_ints_ops(expr, ctxt):
    if expr.op == TO_REAL:
        return typecheck_to_real(expr, ctxt)
    if expr.op == TO_INT:
        return typecheck_to_int(expr, ctxt)
    if expr.op == IS_INT:
        return typecheck_is_int(expr, ctxt)


def typecheck_let_expression(expr, ctxt):
    n_var_binders = len(expr.var_binders)
    for i in range(n_var_binders):
        var = expr.var_binders[i]
        t = typecheck_expr(expr.let_terms[i], ctxt)
        ctxt.add_to_locals(var, t)
    return typecheck_expr(expr.subterms[0], ctxt)


def typecheck_label(expr, ctxt):
    return typecheck_expr(expr.subterms[0], ctxt)


def typecheck_to_fp_unsigned(expr, ctxt):
    """
    ((_ to_fp_unsigned eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
    """  # noqa: 501
    eb, sb = int(expr.op.split(" ")[2]), int(expr.op.split(" ")[3].strip(")"))
    t1 = typecheck_expr(expr.subterms[0], ctxt)
    t2 = typecheck_expr(expr.subterms[1], ctxt)
    if not isinstance(t1, ROUNDINGMODE_TYPE)\
       or isinstance(t2, BITVECTOR_TYPE):
        raise TypeCheckError(expr)
    return FP_TYPE(eb, sb)


def typecheck_to_fp(expr, ctxt):
    """
    ((_ to_fp eb sb) (_ BitVec m) (_ FloatingPoint eb sb))
    ((_ to_fp eb sb) RoundingMode (_ FloatingPoint mb nb) (_ FloatingPoint eb sb))
    ((_ to_fp eb sb) RoundingMode Real (_ FloatingPoint eb sb))
    ((_ to_fp eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
    """  # noqa: E501
    eb, sb = int(expr.op.split(" ")[2]), int(expr.op.split(" ")[3].strip(")"))
    if len(expr.subterms) == 1:
        bv = expr.subterms[0]
        t = typecheck_expr(expr.subterms[0], ctxt)
        if not isinstance(t, BITVECTOR_TYPE):
            raise TypeCheckError(expr, bv, BITVECTOR_TYPE, t)

    if len(expr.subterms) == 2:
        t1 = typecheck_expr(expr.subterms[0], ctxt)
        t2 = typecheck_expr(expr.subterms[1], ctxt)
        if (
            not (isinstance(t1, ROUNDINGMODE_TYPE) and isinstance(t2, FP_TYPE))
            or not (isinstance(t1, ROUNDINGMODE_TYPE) and t2 == REAL_TYPE)
            or not (
                isinstance(t1, ROUNDINGMODE_TYPE) and
                isinstance(t2, BITVECTOR_TYPE)
            )
        ):
            raise TypeCheckError(expr)

    return FP_TYPE(eb, sb)


def annotate(f, expr, ctxt):
    """
    f: function argument
    expr: expression
    ctxt: context
    :returns: type of expr
    """
    t = f(expr, ctxt)
    expr.type = t
    return t


def typecheck_expr(expr, ctxt=Context({}, {})):
    if expr.is_const:
        return expr.type
    if expr.is_var or expr.is_indexed_id:
        if expr.name in ctxt.locals:
            expr.type = ctxt.locals[expr.name]
            return ctxt.locals[expr.name]
        elif expr.name in ctxt.globals:
            expr.type = ctxt.globals[expr.name]
            return ctxt.globals[expr.name]
        return UNKNOWN
    elif expr.op:
        if expr.op in CORE_OPS:
            return annotate(typecheck_core, expr, ctxt)
        if expr.op in NUMERICAL_OPS:
            return annotate(typecheck_numeral, expr, ctxt)
        if expr.op in INT_OPS:
            return annotate(typecheck_int_ops, expr, ctxt)
        if expr.op in REAL_OPS:
            return annotate(typecheck_real_ops, expr, ctxt)
        if expr.op in REAL_INTS:
            return annotate(typecheck_real_ints_ops, expr, ctxt)
        if expr.op in STRING_OPS:
            return annotate(typecheck_string_ops, expr, ctxt)
        if expr.op in ARRAY_OPS:
            return annotate(typecheck_array_ops, expr, ctxt)
        if expr.op in FP_OPS:
            return annotate(typecheck_fp_ops, expr, ctxt)
        if expr.op in BV_OPS:
            return annotate(typecheck_bv_ops, expr, ctxt)

        # FP infix ops
        if TO_FP in expr.op:
            return annotate(typecheck_to_fp, expr, ctxt)

        if TO_FP_UNSIGNED in expr.op:
            return annotate(typecheck_to_fp_unsigned, expr, ctxt)

        # BV infix ops
        if (
            BV_EXTRACT in expr.op
            or BV_ZERO_EXTEND in expr.op
            or BV_SIGN_EXTEND in expr.op
        ):
            return annotate(typecheck_bv_unary, expr, ctxt)

        key = expr.op.__str__()
        if key in ctxt.globals:
            t = ctxt.globals[key].split(" ")[-1]
            expr.type = t
            return t
        raise UnknownOperator(expr.op)

    elif expr.quantifier:
        return annotate(typecheck_quantifiers, expr, ctxt)
    elif expr.let_terms:
        return annotate(typecheck_let_expression, expr, ctxt)
    elif expr.label:
        return annotate(typecheck_label, expr, ctxt)
    return UNKNOWN


def typecheck(formula, glob):
    """
    :formula: Script object representing formula
    :glob: glob variables for formula returned by parser
    :returns: context object ctxt
    """
    ctxt = Context(glob, {})
    for cmd in formula.commands:
        if isinstance(cmd, Assert):
            typecheck_expr(cmd.term, ctxt)
    return ctxt
