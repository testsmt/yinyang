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

import re

from ffg.gen.gen_configuration import (
    BOOLEAN_OPTION,
    REAL_OPTION,
    INT_OPTION,
    STRING_OPTION,
    BITVECTOR_OPTION
)

BOOLEAN_TYPE = "Bool"
REAL_TYPE = "Real"
INTEGER_TYPE = "Int"
ROUNDINGMODE_TYPE = "RoundingMode"
STRING_TYPE = "String"
REGEXP_TYPE = "RegLan"
UNKNOWN = "Unknown"
ALL = "A"

TYPES = [
    BOOLEAN_TYPE,
    REAL_TYPE,
    INTEGER_TYPE,
    STRING_TYPE,
    REGEXP_TYPE,
    ROUNDINGMODE_TYPE,
]


def type2ffg(typ):
    if typ == BOOLEAN_TYPE:
        return BOOLEAN_OPTION
    elif typ == REAL_TYPE:
        return REAL_OPTION
    elif typ == INTEGER_TYPE:
        return INT_OPTION
    elif typ == STRING_TYPE:
        return STRING_OPTION
    elif isinstance(typ, BITVECTOR_TYPE):
        # TODO: manage also the size
        return BITVECTOR_OPTION
    else:
        # If the type is not supported by ffg.
        return None


def parse_sexpr(s):
    """
    Parse an s-expression such as a sort, e.g. "(Array Int (_ BitVec 8))",
    into nested lists of tokens: ["Array", "Int", ["_", "BitVec", "8"]].
    Quoted symbols (|...|) are kept as one token.

    :raises ValueError: if the parentheses are not balanced
    """
    tokens = re.findall(r"\|[^|]*\||[()]|[^\s()|]+", s)
    stack = [[]]
    for token in tokens:
        if token == "(":
            stack.append([])
        elif token == ")":
            if len(stack) == 1:
                raise ValueError("unbalanced s-expression: " + s)
            closed = stack.pop()
            stack[-1].append(closed)
        else:
            stack[-1].append(token)
    if len(stack) != 1 or len(stack[0]) != 1:
        raise ValueError("not a single s-expression: " + s)
    return stack[0][0]


def sexpr2str(tree):
    if isinstance(tree, list):
        return "(" + " ".join(sexpr2str(t) for t in tree) + ")"
    return tree


# Sort aliases of the FloatingPoint theory and their (eb, sb).
FP_SORT_ALIASES = {
    "Float16": (5, 11),
    "Float32": (8, 24),
    "Float64": (11, 53),
    "Float128": (15, 113),
}


def _tree2type(tree):
    if isinstance(tree, str):
        if tree in FP_SORT_ALIASES:
            return FP_TYPE(*FP_SORT_ALIASES[tree])
        return tree
    if len(tree) == 3 and tree[:2] == ["_", "BitVec"]:
        return BITVECTOR_TYPE(int(tree[2]))
    if len(tree) == 4 and tree[:2] == ["_", "FloatingPoint"]:
        return FP_TYPE(int(tree[2]), int(tree[3]))
    if len(tree) == 3 and tree[0] == "Array":
        return ARRAY_TYPE(_tree2type(tree[1]), _tree2type(tree[2]))
    # Other parametric sorts, e.g. (Seq Int) or user-defined (List Int).
    return sexpr2str(tree)


def sort2type(sort):
    """
    Convert a sort, e.g. "(_ BitVec 8)", "Float32" or "(Array Int Real)",
    into a type: BITVECTOR_TYPE, FP_TYPE, ARRAY_TYPE, or the sort string
    itself for all other sorts (Int, Bool, user-defined sorts, ...).
    """
    if not isinstance(sort, str):
        return sort
    try:
        tree = parse_sexpr(sort)
        return _tree2type(tree)
    except (ValueError, IndexError):
        return sort


class _SortType:
    """
    Base class of the structured types. Types are compared and hashed by
    their SMT-LIB sort, and compare equal to the sort string, e.g.
    BITVECTOR_TYPE(8) == "(_ BitVec 8)".
    """

    def __eq__(self, other):
        if isinstance(other, (_SortType, str)):
            return str(self) == str(other)
        return NotImplemented

    def __ne__(self, other):
        result = self.__eq__(other)
        if result is NotImplemented:
            return result
        return not result

    def __hash__(self):
        return hash(str(self))

    def __repr__(self):
        return str(self)


class ARRAY_TYPE(_SortType):
    def __init__(self, index_type, payload_type):
        self.index_type = index_type
        self.payload_type = payload_type

    def __str__(self):
        # (Array index_type payload_type)
        return "(Array %s %s)" % (self.index_type, self.payload_type)


class BITVECTOR_TYPE(_SortType):
    def __init__(self, bitwidth):
        self.bitwidth = bitwidth

    def __str__(self):
        #  (_ BitVec bitwidth)
        return "(_ BitVec " + str(self.bitwidth) + ")"


class FP_TYPE(_SortType):
    def __init__(self, eb, sb):
        self.eb = eb
        self.sb = sb

    def __str__(self):
        # (_ FloatingPoint eb sb)
        return "(_ FloatingPoint " + str(self.eb) + " " + str(self.sb) + ")"


class FUNCTION_TYPE(_SortType):
    """
    Type of a function symbol: declared and defined functions, datatype
    constructors, selectors and testers.
    """

    def __init__(self, arg_types, ret_type):
        self.arg_types = list(arg_types)
        self.ret_type = ret_type

    def __str__(self):
        # (arg_type1 ... arg_typen) ret_type
        return "(%s) %s" % (" ".join(str(t) for t in self.arg_types),
                            self.ret_type)


# Core ops
NOT = "not"
AND = "and"
IMPLIES = "=>"
OR = "or"
XOR = "xor"
EQUAL = "="
DISTINCT = "distinct"
ITE = "ite"

CORE_OPS = [NOT, AND, IMPLIES, OR, XOR, EQUAL, DISTINCT, ITE]

# Numerical ops
UNARY_MINUS = "-"
MINUS = "-"
PLUS = "+"
MULTIPLY = "*"
ABS = "abs"
GTE = ">="
GT = ">"
LTE = "<="
LT = "<"

NUMERICAL_OPS = [UNARY_MINUS, MINUS, PLUS, MULTIPLY, ABS, GTE, GT, LTE, LT]


# specific Int ops
DIV = "div"
MOD = "mod"

INT_OPS = [DIV, MOD]

# specific real ops
REAL_DIV = "/"

REAL_OPS = [REAL_DIV]

# casting ops
TO_REAL = "to_real"
TO_INT = "to_int"
IS_INT = "is_int"

REAL_INTS = [REAL_DIV, TO_REAL, TO_INT, IS_INT]

EQ = [EQUAL, DISTINCT]
RT_BOOL = [NOT, AND, IMPLIES, OR, XOR]

# string ops
CONCAT = "str.++"
STRLEN = "str.len"
LEXORD = "str.<"
STR_TO_RE = "str.to_re"
STR_IN_RE = "str.in_re"
RE_NONE = "re.none"
RE_ALL = "re.all"
RE_ALLCHAR = "re.allchar"
RE_CONCAT = "re.++"
RE_UNION = "re.union"
RE_INTER = "re.inter"
RE_KLENE = "re.*"
REFLEX_CLOS = "str.<="
STR_AT = "str.at"
STR_SUBSTR = "str.substr"
STR_PREFIXOF = "str.prefixof"
STR_SUFFIXOF = "str.suffixof"
STR_CONTAINS = "str.contains"
STR_INDEXOF = "str.indexof"
STR_REPLACE = "str.replace"
STR_REPLACE_ALL = "str.replace_all"
STR_REPLACE_RE = "str.replace_re"
STR_REPLACE_RE_ALL = "str.replace_re_all"
RE_COMP = "re.comp"
RE_DIFF = "re.diff"
RE_PLUS = "re.+"
RE_OPT = "re.opt"
RE_RANGE = "re.range"
STR_IS_DIGIT = "str.is_digit"
STR_TO_CODE = "str.to_code"
STR_TO_INT = "str.to_int"
STR_FROM_CODE = "str.from_code"
STR_FROM_INT = "str.from_int"

STRING_OPS = [
    CONCAT,
    STRLEN,
    LEXORD,
    STR_TO_RE,
    STR_IN_RE,
    RE_NONE,
    RE_ALL,
    RE_ALLCHAR,
    RE_CONCAT,
    RE_UNION,
    RE_INTER,
    RE_KLENE,
    REFLEX_CLOS,
    STR_AT,
    STR_SUBSTR,
    STR_PREFIXOF,
    STR_SUFFIXOF,
    STR_CONTAINS,
    STR_INDEXOF,
    STR_REPLACE,
    STR_REPLACE_ALL,
    STR_REPLACE_RE,
    STR_REPLACE_RE_ALL,
    RE_COMP,
    RE_DIFF,
    RE_PLUS,
    RE_OPT,
    RE_RANGE,
    STR_IS_DIGIT,
    STR_TO_CODE,
    STR_TO_INT,
    STR_FROM_CODE,
    STR_FROM_INT,
]

# Array ops
SELECT = "select"
STORE = "store"
ARRAY_OPS = [SELECT, STORE]

# Bitvector ops
BV_CONCAT = "concat"
BVNOT = "bvnot"
BVNEG = "bvneg"
BVAND = "bvand"
BVOR = "bvor"
BVXOR = "bvxor"
BVNAND = "bvnand"
BVNOR = "bvnor"
BVXNOR = "bvxnor"
BVADD = "bvadd"
BVSUB = "bvsub"
BVMUL = "bvmul"
BVUDIV = "bvudiv"
BVUREM = "bvurem"
BVSDIV = "bvsdiv"
BVSREM = "bvsrem"
BVSMOD = "bvsmod"
BVSHL = "bvshl"
BVLSHR = "bvlshr"
BVASHR = "bvashr"
BVCOMP = "bvcomp"
BVULT = "bvult"
BVULE = "bvule"
BVUGT = "bvugt"
BVUGE = "bvuge"
BVSLT = "bvslt"
BVSLE = "bvsle"
BVSGT = "bvsgt"
BVSGE = "bvsge"

# (op (_ BitVec m) (_ BitVec m) (_ BitVec m))
BV_BINARY_OPS = [
    BVAND, BVOR, BVXOR, BVNAND, BVNOR, BVXNOR, BVADD, BVSUB, BVMUL, BVUDIV,
    BVUREM, BVSDIV, BVSREM, BVSMOD, BVSHL, BVLSHR, BVASHR,
]

# (op (_ BitVec m) (_ BitVec m) Bool)
BV_COMPARISON_OPS = [
    BVULT, BVULE, BVUGT, BVUGE, BVSLT, BVSLE, BVSGT, BVSGE,
]

BV_OPS = [BV_CONCAT, BVNOT, BVNEG, BVCOMP] + BV_BINARY_OPS + BV_COMPARISON_OPS

# Indexed ops ((_ op i ...) (_ BitVec m) ...), by their name
BV_INDEXED_OPS = [
    "extract", "zero_extend", "sign_extend", "repeat", "rotate_left",
    "rotate_right",
]

BV_EXTRACT = "(_ extract"
BV_ZERO_EXTEND = "(_ zero_extend"
BV_SIGN_EXTEND = "(_ sign_extend"

# Floating Point ops
FP_ABS = "fp.abs"
FP_NEG = "fp.neg"
FP_ADD = "fp.add"
FP_SUB = "fp.sub"
FP_MUL = "fp.mul"
FP_DIV = "fp.div"
FP_SQRT = "fp.sqrt"
FP_REM = "fp.rem"
FP_ROUND_TO_INTEGRAL = "fp.roundToIntegral"
FP_FMA = "fp.fma"
FP_MIN = "fp.min"
FP_MAX = "fp.max"
FP_LEQ = "fp.leq"
FP_LT = "fp.lt"
FP_GEQ = "fp.geq"
FP_GT = "fp.gt"
FP_EQ = "fp.eq"
FP_NORMAL = "fp.isNormal"
FP_ISSUBNORMAL = "fp.isSubnormal"
FP_IS_ZERO = "fp.isZero"
FP_ISINFINITE = "fp.isInfinite"
FP_ISNAN = "fp.isNaN"
FP_ISNEGATIVE = "fp.isNegative"
FP_ISPOSITIVE = "fp.isPositive"

FP_OPS = [
    FP_ABS,
    FP_NEG,
    FP_ADD,
    FP_SUB,
    FP_MUL,
    FP_DIV,
    FP_SQRT,
    FP_REM,
    FP_ROUND_TO_INTEGRAL,
    FP_FMA,
    FP_MIN,
    FP_MAX,
    FP_LEQ,
    FP_LT,
    FP_GEQ,
    FP_GT,
    FP_EQ,
    FP_NORMAL,
    FP_ISSUBNORMAL,
    FP_IS_ZERO,
    FP_ISINFINITE,
    FP_ISNAN,
    FP_ISNEGATIVE,
    FP_ISPOSITIVE,
]

FP_TO_REAL = "fp.to_real"
FP_CTOR = "fp"
FP_OPS.append(FP_TO_REAL)

# Indexed FP ops ((_ op i ...) ...), by their name
TO_FP = "to_fp"
TO_FP_UNSIGNED = "to_fp_unsigned"
FP_INDEXED_OPS = [TO_FP, TO_FP_UNSIGNED, "fp.to_ubv", "fp.to_sbv"]

# Rounding modes and indexed FP constants such as (_ +zero 8 24)
ROUNDING_MODES = [
    "RNE", "RNA", "RTP", "RTN", "RTZ", "roundNearestTiesToEven",
    "roundNearestTiesToAway", "roundTowardPositive", "roundTowardNegative",
    "roundTowardZero",
]
FP_INDEXED_CONSTANTS = ["+zero", "-zero", "+oo", "-oo", "NaN"]

# Quantifiers
EXISTS = "exists"
FORALL = "forall"
