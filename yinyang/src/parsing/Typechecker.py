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

from yinyang.src.parsing.Types import (
    sort2type, parse_sexpr, sexpr2str,
    # Types
    BOOLEAN_TYPE, REAL_TYPE, INTEGER_TYPE, ROUNDINGMODE_TYPE, STRING_TYPE,
    REGEXP_TYPE, UNKNOWN, ARRAY_TYPE, BITVECTOR_TYPE, FP_TYPE, FUNCTION_TYPE,
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
    BVNEG, BVCOMP, BV_BINARY_OPS, BV_COMPARISON_OPS, BV_INDEXED_OPS,
    FP_ABS, FP_NEG, FP_ADD, FP_SUB, FP_MUL, FP_DIV, FP_SQRT, FP_REM,
    FP_ROUND_TO_INTEGRAL, FP_NORMAL, FP_ISSUBNORMAL, FP_IS_ZERO,
    FP_ISINFINITE, FP_ISNAN, FP_ISNEGATIVE, FP_ISPOSITIVE, FP_LEQ, FP_LT,
    FP_GEQ, FP_GT, FP_EQ, FP_MIN, FP_MAX, FP_FMA, FP_TO_REAL, FP_CTOR,
    FP_INDEXED_OPS,
)

from yinyang.src.parsing.Ast import Assert, Term


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
        self.message = "Ill-typed expression \nterm: \t \t"\
                       + str(expr) + "\n"
        if isinstance(subterm, list):
            subterm = "[" + " ".join(str(term) for term in subterm) + "]"
        self.message += "faulty subterm:\t" + str(subterm) + "\n"
        self.message += "expected: \t" + str(expected) + "\n"
        self.message += "actual: \t" + str(actual)
        super().__init__(self.message)


class UnknownOperator(Exception):
    def __init__(self, op):
        self.message = "unknown function/constant " + str(op)
        # sys.tracebacklimit = 0
        super().__init__(self.message)


def is_subtype(t, tprime):
    """
    Int is accepted where Real is expected: z3 and cvc5 accept mixed
    Int/Real arithmetic, e.g. (+ x 1) with x Real.
    """
    return t == INTEGER_TYPE and tprime == REAL_TYPE


def compatible(t, tprime):
    return t == tprime or is_subtype(t, tprime) or is_subtype(tprime, t)


def join(t, tprime):
    """The common type of two compatible types."""
    return REAL_TYPE if REAL_TYPE in (t, tprime) and t != tprime else t


def check_arg(expr, term, expected, ctxt):
    """Typecheck term, an argument of expr, against the expected type."""
    t = typecheck_expr(term, ctxt)
    if not (t == expected or is_subtype(t, expected)):
        raise TypeCheckError(expr, term, expected, t)
    return t


def check_arity(expr, n, at_least=False):
    m = len(expr.subterms)
    if m < n or (m != n and not at_least):
        raise TypeCheckError(
            expr, expr, ("at least " if at_least else "") + "%d arguments" % n,
            "%d arguments" % m
        )


def typecheck_not(expr, ctxt=[]):
    """(not Bool Bool)"""
    check_arity(expr, 1)
    check_arg(expr, expr.subterms[0], BOOLEAN_TYPE, ctxt)
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
    return typ


def typecheck_nary_numeral_ret(expr, ctxt=[]):
    """(- Int Int Int :left-assoc)
    (+ Int Int Int :left-assoc)
    (* Int Int Int :left-assoc)
    (- Real Real Real :left-assoc)
    (+ Real Real Real :left-assoc)
    (* Real Real Real :left-assoc)

    The result is Real if any argument is Real (mixed Int/Real arithmetic
    as accepted by z3 and cvc5), Int otherwise.
    """
    check_arity(expr, 2, at_least=True)
    typ = INTEGER_TYPE
    for term in expr.subterms:
        t = typecheck_expr(term, ctxt)
        if t not in [INTEGER_TYPE, REAL_TYPE]:
            raise TypeCheckError(expr, term, [INTEGER_TYPE, REAL_TYPE], t)
        typ = join(typ, t)
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


def typecheck_eq(expr, ctxt=[]):
    """(par (A) (= A A Bool :chainable))
    (par (A) (distinct A A Bool :pairwise))
    """
    check_arity(expr, 2, at_least=True)
    typ = typecheck_expr(expr.subterms[0], ctxt)
    for term in expr.subterms[1:]:
        t = typecheck_expr(term, ctxt)
        if not compatible(t, typ):
            raise TypeCheckError(expr, term, typ, t)
    return BOOLEAN_TYPE


def typecheck_ite(expr, ctxt=[]):
    """(par (A) (ite Bool A A A))"""
    check_arity(expr, 3)
    check_arg(expr, expr.subterms[0], BOOLEAN_TYPE, ctxt)
    t1 = typecheck_expr(expr.subterms[1], ctxt)
    t2 = typecheck_expr(expr.subterms[2], ctxt)
    if not compatible(t1, t2):
        raise TypeCheckError(expr, expr.subterms[2], t1, t2)
    return join(t1, t2)


def typecheck_nary_bool(expr, ctxt=[]):
    """
    (and Bool Bool Bool :left-assoc)
    (or Bool Bool Bool :left-assoc)
    (xor Bool Bool Bool :left-assoc)
    (=> Bool Bool Bool :right-assoc)
    """
    for term in expr.subterms:
        check_arg(expr, term, BOOLEAN_TYPE, ctxt)
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
    check_arity(expr, 2, at_least=True)
    for term in expr.subterms:
        t = typecheck_expr(term, ctxt)
        if t not in [INTEGER_TYPE, REAL_TYPE]:
            raise TypeCheckError(expr, term, [INTEGER_TYPE, REAL_TYPE], t)
    return BOOLEAN_TYPE


def typecheck_to_real(expr, ctxt):
    """(to_real Int Real)"""
    t = typecheck_expr(expr.subterms[0], ctxt)
    if t != INTEGER_TYPE:
        raise TypeCheckError(expr, expr.subterms[0], INTEGER_TYPE, t)
    return REAL_TYPE


def typecheck_to_int(expr, ctxt):
    """(to_int Real Int)"""
    t = typecheck_expr(expr.subterms[0], ctxt)
    if t not in [REAL_TYPE, INTEGER_TYPE]:
        raise TypeCheckError(expr, expr.subterms[0], REAL_TYPE, t)
    return INTEGER_TYPE


def typecheck_is_int(expr, ctxt):
    """(is_int Real Bool)"""
    t = typecheck_expr(expr.subterms[0], ctxt)
    if t not in [REAL_TYPE, INTEGER_TYPE]:
        raise TypeCheckError(expr, expr.subterms[0], REAL_TYPE, t)
    return BOOLEAN_TYPE


def typecheck_real_div(expr, ctxt):
    """(/ Real Real Real :left-assoc)"""
    for term in expr.subterms:
        t = typecheck_expr(term, ctxt)
        if t not in [REAL_TYPE, INTEGER_TYPE]:
            raise TypeCheckError(expr, term, REAL_TYPE, t)
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
    check_arity(expr, 2)
    array_type = typecheck_expr(expr.subterms[0], ctxt)
    if not isinstance(array_type, ARRAY_TYPE):
        raise TypeCheckError(expr, expr.subterms[0], "(Array X Y)",
                             array_type)
    check_arg(expr, expr.subterms[1], array_type.index_type, ctxt)
    return array_type.payload_type


def typecheck_store(expr, ctxt):
    """
    (store (Array X Y) X Y (Array X Y)))
    """
    check_arity(expr, 3)
    array_type = typecheck_expr(expr.subterms[0], ctxt)
    if not isinstance(array_type, ARRAY_TYPE):
        raise TypeCheckError(expr, expr.subterms[0], "(Array X Y)",
                             array_type)
    check_arg(expr, expr.subterms[1], array_type.index_type, ctxt)
    check_arg(expr, expr.subterms[2], array_type.payload_type, ctxt)
    return array_type


def typecheck_array_ops(expr, ctxt):
    if expr.op == SELECT:
        return typecheck_select(expr, ctxt)
    if expr.op == STORE:
        return typecheck_store(expr, ctxt)


def bv_args(expr, ctxt, same_width=True):
    """
    Typecheck the arguments of expr as bit-vectors.
    :returns: the list of their types
    """
    types = []
    for term in expr.subterms:
        t = typecheck_expr(term, ctxt)
        if not isinstance(t, BITVECTOR_TYPE):
            raise TypeCheckError(expr, term, "(_ BitVec m)", t)
        if same_width and types and t != types[0]:
            raise TypeCheckError(expr, term, types[0], t)
        types.append(t)
    return types


def typecheck_bv_ops(expr, ctxt):
    """
    (concat (_ BitVec i) (_ BitVec j) (_ BitVec i+j))
    (bvnot (_ BitVec m) (_ BitVec m)), also bvneg
    (bvand (_ BitVec m) (_ BitVec m) (_ BitVec m)), also BV_BINARY_OPS
    (bvult (_ BitVec m) (_ BitVec m) Bool), also BV_COMPARISON_OPS
    (bvcomp (_ BitVec m) (_ BitVec m) (_ BitVec 1))
    """
    if expr.op == BV_CONCAT:
        check_arity(expr, 2, at_least=True)
        types = bv_args(expr, ctxt, same_width=False)
        return BITVECTOR_TYPE(sum(t.bitwidth for t in types))
    if expr.op in [BVNOT, BVNEG]:
        check_arity(expr, 1)
        return bv_args(expr, ctxt)[0]
    if expr.op in BV_BINARY_OPS:
        # z3 and cvc5 also accept more than two arguments
        check_arity(expr, 2, at_least=True)
        return bv_args(expr, ctxt)[0]
    if expr.op in BV_COMPARISON_OPS:
        check_arity(expr, 2)
        bv_args(expr, ctxt)
        return BOOLEAN_TYPE
    if expr.op == BVCOMP:
        check_arity(expr, 2)
        bv_args(expr, ctxt)
        return BITVECTOR_TYPE(1)


def typecheck_bv_indexed(expr, ctxt, name, indices):
    """
    ((_ extract i j) (_ BitVec m) (_ BitVec i-j+1)), m > i >= j >= 0
    ((_ zero_extend i) (_ BitVec m) (_ BitVec m+i)), also sign_extend
    ((_ repeat i) (_ BitVec m) (_ BitVec i*m))
    ((_ rotate_left i) (_ BitVec m) (_ BitVec m)), also rotate_right
    """
    check_arity(expr, 1)
    m = bv_args(expr, ctxt)[0].bitwidth
    if name == "extract":
        i, j = indices
        if not m > i >= j >= 0:
            raise TypeCheckError(expr, expr.subterms[0],
                                 "(_ BitVec m) with m > %d" % i,
                                 BITVECTOR_TYPE(m))
        return BITVECTOR_TYPE(i - j + 1)
    if name in ["zero_extend", "sign_extend"]:
        return BITVECTOR_TYPE(m + indices[0])
    if name == "repeat":
        return BITVECTOR_TYPE(m * indices[0])
    return BITVECTOR_TYPE(m)


def fp_args(expr, terms, ctxt):
    """
    Typecheck terms, arguments of expr, as floating-point numbers of the
    same sort.
    :returns: their type
    """
    typ = None
    for term in terms:
        t = typecheck_expr(term, ctxt)
        if not isinstance(t, FP_TYPE):
            raise TypeCheckError(expr, term, "(_ FloatingPoint eb sb)", t)
        if typ is not None and t != typ:
            raise TypeCheckError(expr, term, typ, t)
        typ = t
    return typ


def typecheck_fp_ops(expr, ctxt):
    """
    (fp.abs (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)), also fp.neg
    (fp.add RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
        (_ FloatingPoint eb sb)), also fp.sub, fp.mul, fp.div
    (fp.fma RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
        (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
    (fp.sqrt RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)),
        also fp.roundToIntegral
    (fp.rem (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
        (_ FloatingPoint eb sb)), also fp.min, fp.max
    (fp.leq (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) Bool
        :chainable), also fp.lt, fp.geq, fp.gt, fp.eq
    (fp.isNormal (_ FloatingPoint eb sb) Bool), also the other fp.is*
    (fp.to_real (_ FloatingPoint eb sb) Real)
    """
    op, args = expr.op, expr.subterms
    if op in [FP_ABS, FP_NEG]:
        check_arity(expr, 1)
        return fp_args(expr, args, ctxt)
    if op in [FP_ADD, FP_SUB, FP_MUL, FP_DIV, FP_FMA, FP_SQRT,
              FP_ROUND_TO_INTEGRAL]:
        n = {FP_FMA: 4, FP_SQRT: 2, FP_ROUND_TO_INTEGRAL: 2}.get(op, 3)
        check_arity(expr, n)
        check_arg(expr, args[0], ROUNDINGMODE_TYPE, ctxt)
        return fp_args(expr, args[1:], ctxt)
    if op in [FP_REM, FP_MIN, FP_MAX]:
        check_arity(expr, 2)
        return fp_args(expr, args, ctxt)
    if op in [FP_LEQ, FP_LT, FP_GEQ, FP_GT, FP_EQ]:
        check_arity(expr, 2, at_least=True)
        fp_args(expr, args, ctxt)
        return BOOLEAN_TYPE
    if op in [FP_NORMAL, FP_ISSUBNORMAL, FP_IS_ZERO, FP_ISINFINITE,
              FP_ISNAN, FP_ISNEGATIVE, FP_ISPOSITIVE]:
        check_arity(expr, 1)
        fp_args(expr, args, ctxt)
        return BOOLEAN_TYPE
    if op == FP_TO_REAL:
        check_arity(expr, 1)
        fp_args(expr, args, ctxt)
        return REAL_TYPE


def typecheck_fp_ctor(expr, ctxt):
    """
    (fp (_ BitVec 1) (_ BitVec eb) (_ BitVec i) (_ FloatingPoint eb i+1))
    """
    check_arity(expr, 3)
    sign, exponent, significand = bv_args(expr, ctxt, same_width=False)
    if sign.bitwidth != 1:
        raise TypeCheckError(expr, expr.subterms[0], BITVECTOR_TYPE(1), sign)
    return FP_TYPE(exponent.bitwidth, significand.bitwidth + 1)


def typecheck_fp_indexed(expr, ctxt, name, indices):
    """
    ((_ to_fp eb sb) (_ BitVec m) (_ FloatingPoint eb sb))
    ((_ to_fp eb sb) RoundingMode (_ FloatingPoint mb nb)
        (_ FloatingPoint eb sb))
    ((_ to_fp eb sb) RoundingMode Real (_ FloatingPoint eb sb))
    ((_ to_fp eb sb) RoundingMode (_ BitVec m) (_ FloatingPoint eb sb))
    ((_ to_fp_unsigned eb sb) RoundingMode (_ BitVec m)
        (_ FloatingPoint eb sb))
    ((_ fp.to_ubv m) RoundingMode (_ FloatingPoint eb sb) (_ BitVec m)),
        also fp.to_sbv
    """
    args = expr.subterms
    if name in ["fp.to_ubv", "fp.to_sbv"]:
        check_arity(expr, 2)
        check_arg(expr, args[0], ROUNDINGMODE_TYPE, ctxt)
        fp_args(expr, args[1:], ctxt)
        return BITVECTOR_TYPE(indices[0])

    eb, sb = indices
    if name == "to_fp" and len(args) == 1:
        t = typecheck_expr(args[0], ctxt)
        if t != BITVECTOR_TYPE(eb + sb):
            raise TypeCheckError(expr, args[0], BITVECTOR_TYPE(eb + sb), t)
        return FP_TYPE(eb, sb)

    check_arity(expr, 2)
    check_arg(expr, args[0], ROUNDINGMODE_TYPE, ctxt)
    t = typecheck_expr(args[1], ctxt)
    if name == "to_fp_unsigned":
        allowed = isinstance(t, BITVECTOR_TYPE)
    else:
        allowed = isinstance(t, (FP_TYPE, BITVECTOR_TYPE)) or \
            t in [REAL_TYPE, INTEGER_TYPE]
    if not allowed:
        raise TypeCheckError(expr, args[1], "FloatingPoint, Real or BitVec",
                             t)
    return FP_TYPE(eb, sb)


def typecheck_quantifiers(expr, ctxt):
    vars = expr.quantified_vars[0]
    types = expr.quantified_vars[1]
    # Bindings must not leak into the surrounding scope: a quantified
    # variable can shadow a global (or an enclosing binder) of the same
    # name, so we save whatever was there before and restore it once the
    # quantifier's body has been checked.
    saved = []
    for i in range(len(vars)):
        var, type = vars[i], types[i]
        had_prev = var in ctxt.locals
        prev = ctxt.locals.get(var)
        ctxt.add_to_locals(var, type)
        saved.append((var, had_prev, prev))
    t = typecheck_expr(expr.subterms[0], ctxt)
    for var, had_prev, prev in reversed(saved):
        if had_prev:
            ctxt.locals[var] = prev
        else:
            del ctxt.locals[var]
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
    if expr.op == ABS:
        return typecheck_nary_int_ret(expr, ctxt)


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
    # Bindings must not leak into the surrounding scope: a let-bound
    # variable can shadow a global (or an enclosing binder) of the same
    # name, so we save whatever was there before and restore it once the
    # let body has been checked. The bound terms are checked in the
    # enclosing scope (let is parallel).
    types = [typecheck_expr(term, ctxt) for term in expr.let_terms]
    saved = []
    for i in range(n_var_binders):
        var = expr.var_binders[i]
        had_prev = var in ctxt.locals
        prev = ctxt.locals.get(var)
        ctxt.add_to_locals(var, types[i])
        saved.append((var, had_prev, prev))
    result = typecheck_expr(expr.subterms[0], ctxt)
    for var, had_prev, prev in reversed(saved):
        if had_prev:
            ctxt.locals[var] = prev
        else:
            del ctxt.locals[var]
    return result


def typecheck_label(expr, ctxt):
    return typecheck_expr(expr.subterms[0], ctxt)


def typecheck_app(expr, ctxt, name, ftype):
    """
    Application of a declared or defined function, or of a datatype
    constructor, selector or tester: (f t1 ... tn) with f of type
    (T1 ... Tn) T.
    """
    if len(expr.subterms) != len(ftype.arg_types):
        raise TypeCheckError(expr, expr, "%d arguments for %s" % (
            len(ftype.arg_types), name), "%d arguments" % len(expr.subterms))
    for term, arg_type in zip(expr.subterms, ftype.arg_types):
        check_arg(expr, term, arg_type, ctxt)
    return ftype.ret_type


def typecheck_as(expr, ctxt, tree):
    """
    Application of a qualified identifier, e.g.
    ((as const (Array X Y)) Y (Array X Y))
    """
    typ = sort2type(sexpr2str(tree[2]))
    if tree[1] == "const":
        check_arity(expr, 1)
        if not isinstance(typ, ARRAY_TYPE):
            raise TypeCheckError(expr, expr, "(Array X Y)", typ)
        check_arg(expr, expr.subterms[0], typ.payload_type, ctxt)
        return typ
    for term in expr.subterms:
        typecheck_expr(term, ctxt)
    return typ


def typecheck_indexed(expr, ctxt, op):
    """
    Application of an indexed operator, e.g. ((_ extract 7 4) x).
    :returns: its type, None if the operator is unknown
    """
    tree = parse_sexpr(op)
    if tree[0] == "as" and len(tree) == 3:
        return typecheck_as(expr, ctxt, tree)
    if tree[0] != "_" or len(tree) < 3:
        return None
    name = tree[1]
    try:
        indices = [int(index) for index in tree[2:]]
    except ValueError:
        return None
    if name in BV_INDEXED_OPS:
        return typecheck_bv_indexed(expr, ctxt, name, indices)
    if name in FP_INDEXED_OPS:
        return typecheck_fp_indexed(expr, ctxt, name, indices)
    if name in ["re.loop", "re.^"]:
        # ((_ re.loop i j) RegLan RegLan), ((_ re.^ n) RegLan RegLan)
        check_arity(expr, 1)
        check_arg(expr, expr.subterms[0], REGEXP_TYPE, ctxt)
        return REGEXP_TYPE
    return None


def annotate(f, expr, ctxt, *args):
    """
    f: function argument
    expr: expression
    ctxt: context
    :returns: type of expr
    """
    t = f(expr, ctxt, *args)
    if t is None:
        raise UnknownOperator(expr.op)
    expr.type = t
    return t


def lookup(name, ctxt):
    if name in ctxt.locals:
        return ctxt.locals[name]
    return ctxt.globals.get(name)


def typecheck_expr(expr, ctxt=Context({}, {})):
    if isinstance(expr, str):
        # Symbols that the parser could not resolve
        raise UnknownOperator(expr)
    if expr.is_const:
        return expr.type
    if expr.is_var or expr.is_indexed_id:
        typ = lookup(expr.name, ctxt)
        if typ is None:
            return UNKNOWN
        expr.type = typ
        return typ
    elif expr.op:
        op = expr.op
        if isinstance(op, Term):
            # The parser resolves declared function symbols to variables.
            op = op.name
        ftype = lookup(op, ctxt)
        if isinstance(ftype, FUNCTION_TYPE):
            return annotate(typecheck_app, expr, ctxt, op, ftype)
        if not isinstance(expr.op, str):
            raise UnknownOperator(op)

        if op in CORE_OPS:
            return annotate(typecheck_core, expr, ctxt)
        if op in NUMERICAL_OPS:
            return annotate(typecheck_numeral, expr, ctxt)
        if op in INT_OPS:
            return annotate(typecheck_int_ops, expr, ctxt)
        if op in REAL_OPS:
            return annotate(typecheck_real_ops, expr, ctxt)
        if op in REAL_INTS:
            return annotate(typecheck_real_ints_ops, expr, ctxt)
        if op in STRING_OPS:
            return annotate(typecheck_string_ops, expr, ctxt)
        if op in ARRAY_OPS:
            return annotate(typecheck_array_ops, expr, ctxt)
        if op in FP_OPS:
            return annotate(typecheck_fp_ops, expr, ctxt)
        if op == FP_CTOR:
            return annotate(typecheck_fp_ctor, expr, ctxt)
        if op in BV_OPS:
            return annotate(typecheck_bv_ops, expr, ctxt)
        if op.startswith("("):
            return annotate(typecheck_indexed, expr, ctxt, op)
        raise UnknownOperator(op)

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
