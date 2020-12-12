BOOLEAN_TYPE="bool"
REAL_TYPE="real"
INTEGER_TYPE="integer"
ROUNDINGMODE_TYPE="roundingmode"
STRING_TYPE="string"
REGEXP_TYPE="regex"
UNKNOWN="unknown"

def sort2type(sort):
    sort = sort.replace("Bool", "bool")
    sort = sort.replace("Real", "real")
    sort = sort.replace("Int", "integer")
    sort = sort.replace("String", "string")
    return sort

class ARRAY_TYPE:
    def __init__(self,index_type, payload_type):
        self.index_type = index_type 
        self.payload_type = payload_type 

    def __eq__(self,other):
        if isinstance(other, self.__class__):  
            return self.index_type == other.index_type and\
                   self.payload_type == other.payload_type  

class BITVECTOR_TYPE:
    def __init__(self, bitwidth):
        self.bitwidth = bitwidth

    def __eq__(self,other):
        if isinstance(other, self.__class__):  
            return self.bitwidth == other.bitwidth

class FP_TYPE:
    def __init__(self, eb, sb):
        self.eb = eb 
        self.sb = sb
    
    def __eq__(self,other):
        if isinstance(other, self.__class__):
            return self.eb == other.eb and self.sb == other.sb


# Core ops
NOT="not"
AND="and"
IMPLIES="=>"
OR="or"
XOR="xor"
EQUAL="="
DISTINCT="distinct"
ITE="ite"

# Numerical ops
UNARY_MINUS="-"
MINUS="-"
PLUS="+"
MULTIPLY="*"
ABS="abs"
GTE=">="
GT=">"
LTE="<="
LT="<"

# specific Int ops 
DIV="div"
MOD="mod"

# specific real ops 
REAL_DIV="/"

# casting ops 
TO_REAL="to_real"
TO_INT="to_int"
IS_INT="is_int"

EQ=[EQUAL,DISTINCT]
RT_BOOL=[NOT, AND, IMPLIES, OR, XOR]

# string ops 
CONCAT="str.++"
STRLEN="str.len"
LEXORD="str.<"
STR_TO_RE="str.to_re"
STR_IN_RE="str.in_re"
RE_NONE="re.none"
RE_ALL="re.all"
RE_ALLCHAR="re.allchar"
RE_CONCAT="re.++"
RE_UNION="re.union"
RE_INTER="re.inter"
RE_KLENE="re.*"
REFLEX_CLOS="str.<="
STR_AT="str.at"
STR_SUBSTR="str.substr"
STR_PREFIXOF="str.prefixof"
STR_SUFFIXOF="str.suffixof"
STR_CONTAINS="str.contains"
STR_INDEXOF="str.indexof"
STR_REPLACE="str.replace"
STR_REPLACE_ALL="str.replace_all"
STR_REPLACE_RE="str.replace_re"
STR_REPLACE_RE_ALL="str.replace_re_all"
RE_COMP="re.comp"
RE_DIFF="re.diff"
RE_PLUS="re.+"
RE_OPT="re.opt"
RE_RANGE="re.range"
STR_IS_DIGIT="str.is_digit"
STR_TO_CODE="str.to_code"
STR_TO_INT="str.to_int"
STR_FROM_CODE="str.from_code"
STR_FROM_INT="str.from_int"

STRING_OPS= [
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
    STR_FROM_INT
]

# Array ops 
SELECT="select"
STORE="store"
ARRAY_OPS=[SELECT, STORE]

# Bitvector ops  
BV_CONCAT="concat" 
BVNOT="bvnot"
BVNEG="bvneg"
BVAND="bvand"
BVOR="bvor"
BVADD="bvadd"
BVMUL="bvmul"
BVUDIV="bvudiv"
BVUREM="bvurem"
BVSHL="bvshl"
BVLSHR="bvlshr"
BVULT="bvult"

BV_OPS=[
    BV_CONCAT,
    BVNOT,
    BVNEG, 
    BVAND,
    BVOR,
    BVADD,
    BVMUL,
    BVUDIV,
    BVUREM,
    BVSHL,
    BVLSHR,
    BVULT
]

# Floating Point ops 
FP_ABS="fp.abs"
FP_NEG="fp.neg"
FP_ADD="fp.add"
FP_SUB="fp.sub"
FP_MUL="fp.mul"
FP_DIV="fp.div"
FP_SQRT="fp.sqrt"
FP_REM="fp.rem"
FP_ROUND_TO_INTEGRAL="fp.roundToIntegral"
FP_FMA="fp.fma"
FP_MIN="fp.min"
FP_MAX="fp.max"
FP_LEQ="fp.leq"
FP_LT="fp.lt"
FP_GEQ="fp.geq"
FP_GT="fp.gt" 
FP_EQ="fp.eq"
FP_NORMAL="fp.isNormal"
FP_ISSUBNORMAL="fp.isSubnormal"
FP_IS_ZERO="fp.isZero"
FP_ISINFINITE="fp.isInfinite"
FP_ISNAN="fp.isNan"
FP_ISNEGATIVE="fp.isNegative"
FP_ISPOSITIVE="fp.isPositive"

FP_OPS=[
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
    FP_ISPOSITIVE
]

# Quantifiers
EXISTS="exists"
FORALL="forall"
