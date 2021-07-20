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


def sort2type(sort):
    if "FloatingPoint" in sort:
        eb = int(sort.split(" ")[2])
        sb = int(sort.split(" ")[3][:-1])
        return FP_TYPE(eb, sb)

    if "BitVec" in sort:
        bitwith = int(sort.split(" ")[2][:-1])
        return BITVECTOR_TYPE(bitwith)
    return sort


class ARRAY_TYPE:
    def __init__(self, index_type, payload_type):
        self.index_type = index_type
        self.payload_type = payload_type

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return (
                self.index_type == other.index_type
                and self.payload_type == other.payload_type
            )


class BITVECTOR_TYPE:
    def __init__(self, bitwidth):
        self.bitwidth = bitwidth

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return self.bitwidth == other.bitwidth

        if isinstance(other, str):
            return self.__str__() == other

    def __str__(self):
        #  (_ BitVec bitwidth)
        return "(_ BitVec " + str(self.bitwidth) + ")"


class FP_TYPE:
    def __init__(self, eb, sb):
        self.eb = eb
        self.sb = sb

    def __eq__(self, other):
        if isinstance(other, self.__class__):
            return self.eb == other.eb and self.sb == other.sb
        if isinstance(other, str):
            return self.__str__() == other

    def __str__(self):
        # (_ FloatingPoint eb sb)
        return "(_ FloatingPoint " + str(self.eb) + " " + str(self.sb) + ")"


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
BVADD = "bvadd"
BVSUB = "bvsub"
BVMUL = "bvmul"
BVUDIV = "bvudiv"
BVUREM = "bvurem"
BVSHL = "bvshl"
BVLSHR = "bvlshr"
BVASHR = "bvashr"
BVULT = "bvult"
BVULE = "bvule"
BVSLT = "bvslt"
BVSGT = "bvsgt"
BVSDIV = "bvsdiv"


BV_OPS = [
    BV_CONCAT,
    BVNOT,
    BVNEG,
    BVAND,
    BVOR,
    BVXOR,
    BVADD,
    BVSUB,
    BVMUL,
    BVUDIV,
    BVUREM,
    BVSHL,
    BVASHR,
    BVLSHR,
    BVULT,
    BVULE,
    BVSLT,
    BVSGT,
    BVSDIV,
]

"""
All function symbols with declaration of the form

  ((_ extract i j) (_ BitVec m) (_ BitVec n))

where
- i, j, m, n are numerals
- m > i >= j >= 0,
- n = i - j + 1
"""

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

# FP infix ops
TO_FP = "to_fp"
TO_FP_UNSIGNED = "to_fp_unsigned"

# Quantifiers
EXISTS = "exists"
FORALL = "forall"
