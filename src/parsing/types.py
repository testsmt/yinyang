BOOLEAN_TYPE="bool"
REAL_TYPE="real"
INTEGER_TYPE="integer"
ROUNDINGMODE_TYPE="roundingmode"
STRING_TYPE="string"
REGEXP_TYPE="regex"
UNKNOWN="unknown"

# class ARRAY_TYPE():
    # def __init__(self,index, content):
        # self.index_type = index 
        # self.content_type = content 


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
