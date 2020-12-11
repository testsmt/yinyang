import sys
sys.setrecursionlimit(100000)

from src.parsing.ast_visitor import *
from src.parsing.parse import *
from src.parsing.types import *

# TODO: make a difference between chainable and non-chainable ops  

# TODO: give more meaningful expression  
class TypeCheckError(Exception):
    def __init__(self, expr):
        self.message="(error Typechecker: Ill-typed expression) \nexpr: " + expr.__str__() 
        super().__init__(self.message)

def typecheck_not(expr, ctxt=[]):
    """ (not Bool Bool) """
    if typecheck_expr(expr.subterms[0],ctxt) != BOOLEAN_TYPE:
        raise TypeCheckError(expr)
    return BOOLEAN_TYPE

def typecheck_unary_minus(expr,ctxt=[]):
    """ (- Int Int) """
    """ (- Real Real) """
    if not typecheck_expr(expr.subterms[0],ctxt) in [INTEGER_TYPE, REAL_TYPE]:
        raise TypeCheckError(expr)
    return typecheck_expr(expr.subterms[0],ctxt)

def typecheck_nary_numeral_ret(expr, ctxt=[]):
    """ (- Int Int Int :left-assoc) 
        (+ Int Int Int :left-assoc)
        (* Int Int Int :left-assoc)
        (- Real Real Real :left-assoc) 
        (+ Real Real Real :left-assoc) 
        (* Real Real Real :left-assoc)
        (/ Real Real Real :left-assoc)
    """
    typ = typecheck_expr(expr.subterms[0],ctxt)
    if typ not in [INTEGER_TYPE, REAL_TYPE]:
        raise TypeCheckError(expr) 

    for term in expr.subterms[1:]:
        if typecheck_expr(term,ctxt) != typ:
           raise TypeCheckError(expr) 
    return typ 

def typecheck_nary_int_ret(expr, ctxt=[]):
    """ (div Int Int Int :left-assoc)
        (mod Int Int Int)
        (abs Int Int)
    """
    for term in expr.subterms:
        if typecheck_expr(term,ctxt) != INTEGER_TYPE:
           raise TypeCheckError(expr) 
    return INTEGER_TYPE 

def typecheck_eq(expr, ctxt=[]):
    """ (par (A) (= A A Bool :chainable))
        (par (A) (distinct A A Bool :pairwise))
    """
    typ = typecheck_expr(expr.subterms[0],ctxt)
    for term in expr.subterms[1:]:
        if typecheck_expr(term,ctxt) != typ:
           raise TypeCheckError(expr) 
    return BOOLEAN_TYPE

def typecheck_ite(expr, ctxt=[]):
    """ (par (A) (ite Bool A A A)) """
    if typecheck_expr(expr.subterms[0],ctxt) != BOOLEAN_TYPE and\
        typecheck_expr(expr.subterms[1],ctxt) != typecheck_expr(expr.subterms[2],ctxt):
        raise TypeCheckError(expr)
    return typecheck_expr(expr.subterms[1],ctxt)

def typecheck_nary_bool(expr, ctxt=[]):
    """ (and Bool Bool Bool :left-assoc)
        (or Bool Bool Bool :left-assoc)
        (xor Bool Bool Bool :left-assoc)
    """
    for term in expr.subterms:
        if typecheck_expr(term, ctxt) != BOOLEAN_TYPE:
            raise TypeCheckError(expr)
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
    typ = typecheck_expr(expr.subterms[0],ctxt)
    if typ not in [INTEGER_TYPE, REAL_TYPE]:
        raise TypeCheckError(expr) 
    for term in expr.subterms[1:]:
        if typecheck_expr(term, ctxt) not in [INTEGER_TYPE, REAL_TYPE]:
            raise TypeCheckError(expr)
    return BOOLEAN_TYPE

def typecheck_to_real(expr, ctxt):
    """ (to_real Int Real) """
    if not typecheck(expr,ctxt) == INTEGER_TYPE:
         raise TypeCheckError(expr)
    return REAL_TYPE

def typecheck_to_int(expr, ctxt):
    """ (to_int Real Int) """
    if not typecheck_expr(expr,ctxt) == REAL_TYPE:
         raise TypeCheckError(expr)
    return INTEGER_TYPE

def typecheck_is_int(expr, ctxt): 
    """ (is_int Real Bool) """
    if not typecheck_expr(expr,ctxt) == REAL_TYPE:
        raise TypeCheckError(expr)
    return BOOLEAN_TYPE 

def typecheck_real_div(expr, ctxt): 
    """ (/ Real Real Real :left-assoc) """
    for term in expr.subterms:
        if typecheck_expr(term,ctxt) != REAL_TYPE:
           raise TypeCheckError(expr) 
    return REAL_TYPE 

def typecheck_string_concat(expr, ctxt):
    """ (str.++ String String String :left-assoc)"""
    for term in expr.subterms:
        if typecheck_expr(term, ctxt) != STRING_TYPE:
            raise TypeCheckError(expr)
    return STRING_TYPE 

def typecheck_strlen(expr, ctxt):
    """ (str.len String Int)"""
    if typecheck_expr(expr.subterms[0],ctxt) != STRING_TYPE: 
        raise TypeCheckError(expr)
    return INTEGER_TYPE

def typecheck_nary_string_rt_bool(expr, ctxt):
    """ (str.< String String Bool :chainable) 
        (str.<= String String Bool :chainable)  
        (str.prefixof String String Bool)
        (str.suffixof String String Bool)
        (str.contains String String Bool)
    """
    for term in expr.subterms:
        typ=typecheck_expr(term, ctxt)
        if typecheck_expr(term, ctxt) != STRING_TYPE:
            raise TypeCheckError(expr)
    return BOOLEAN_TYPE

def typecheck_str_to_re(expr, ctxt):
    """ (str.to_re String RegLan) """  
    if typecheck_expr(expr,ctxt) != STRING_TYPE: 
        raise TypeCheckError(expr)
    return REGEXP_TYPE  

def typecheck_regex_consts(expr, ctxt):
    """
    (re.none RegLan)
    (re.all RegLan)
    (re.allchar RegLan)
    """
    return REGEXP_TYPE

def typecheck_str_in_re(expr,ctxt):
    """ (str.in_re String RegLan Bool) """
    if typecheck_expr(expr,ctxt) != REGEXP_TYPE:
        raise TypeCheckError(expr)
    return BOOLEAN_TYPE

def typecheck_regex_unary(expr,ctxt):
    """
    (re.* RegLan RegLan) 
    (re.comp RegLan RegLan)
    (re.opt RegLan RegLan)
    (re.+ RegLan RegLan)
    """
    if typecheck_expr(expr,ctxt) != REGEXP_TYPE:
        raise TypeCheckError(expr)
    return REGEXP_TYPE

def typecheck_regex_binary(expr, ctxt):
    """
    (re.diff RegLan RegLan RegLan :left-assoc)
    (re.++ RegLan RegLan RegLan :left-assoc)
    (re.union RegLan RegLan RegLan :left-assoc)
    (re.inter RegLan RegLan RegLan :left-assoc)
    """
    for term in expr.subterms:
        if not typecheck_expr(term, ctxt) != REGEXP_TYPE:
            raise TypeCheckError(expr)
    return REGEXP_TYPE 
    
def typecheck_str_at(expr,ctxt):
    """ 
    (str.at String Int String)
    """
    if typecheck_expr(expr.subterms[0]) != STRING_TYPE or\
       typecheck_expr(expr.subterms[1]) != INTEGER_TYPE:
        raise TypeCheckError(expr)
    return STRING_TYPE 

def typecheck_substr(expr,ctxt): 
    """
    (str.substr String Int Int String)
    """
    if typecheck_expr(expr.subterms[0]) != STRING_TYPE or\
       typecheck_expr(expr.subterms[1]) != INTEGER_TYPE or\
       typecheck_expr(expr.subterms[2]) != INTEGER_TYPE: 
        raise TypeCheckError(expr)
    return STRING_TYPE 

def typecheck_index_of(expr,ctxt):
    """ (str.indexof String String Int Int) """ 
    if typecheck_expr(expr.subterms[0]) != STRING_TYPE or\
       typecheck_expr(expr.subterms[1]) != STRING_TYPE or\
       typecheck_expr(expr.subterms[2]) != INTEGER_TYPE: 
        raise TypeCheckError(expr)
    return INTEGER_TYPE

def typecheck_replace(expr,ctxt):
    """
    (str.replace String String String String)
    (str.replace_all String String String String)
    """
    if typecheck_expr(expr.subterms[0]) != STRING_TYPE or\
       typecheck_expr(expr.subterms[1]) != STRING_TYPE or\
       typecheck_expr(expr.subterms[2]) != STRING_TYPE: 
        raise TypeCheckError(expr)
    return STRING_TYPE 

def typecheck_replace_re(expr,ctxt):
    """
    (str.replace_re String RegLan String String) 
    (str.replace_re_all String RegLan String String) 
    """
    if typecheck_expr(expr.subterms[0]) != STRING_TYPE or\
       typecheck_expr(expr.subterms[1]) != REGEXP_TYPE or\
       typecheck_expr(expr.subterms[2]) != STRING_TYPE: 
        raise TypeCheckError(expr)
    return STRING_TYPE 

def typecheck_re_range(expr, ctxt):
    """
    (re.range String String RegLan)
    """
    if typecheck_expr(expr.subterms[0]) != STRING_TYPE or\
       typecheck_expr(expr.subterms[1]) != STRING_TYPE: 
        raise TypeCheckError(expr)
    return REGEXP_TYPE 

def typecheck_str_to_int(expr, ctxt):
    """
    (str.to_code String Int) 
    (str.to_int String Int)
    """
    if typecheck_expr(expr.subterms[0]) != STRING_TYPE:
        raise TypeCheckError(expr)
    return INTEGER_TYPE 

def typecheck_is_digit(expr,ctxt):
    """
    (str.is_digit String Bool)
    """
    if typecheck_expr(expr.subterms[0]) != STRING_TYPE:
        raise TypeCheckError(expr)
    return BOOLEAN_TYPE 

def typecheck_int_to_string(expr,ctxt):
    """
    (str.from_code Int String)
    (str.from_int Int String)
    """
    if typecheck_expr(expr.subterms[0]) != INTEGER_TYPE:
        raise TypeCheckError(expr)
    return STRING_TYPE 

def typecheck_string_ops(expr, ctxt):
    if expr.op == CONCAT: 
        return typecheck_string_concat(expr,ctxt)
    if expr.op == STRLEN:
        return typecheck_strlen(expr,ctxt)
    if expr.op in [LEXORD, REFLEX_CLOS, STR_PREFIXOF, STR_SUFFIXOF, STR_CONTAINS]: 
        return typecheck_nary_string_rt_bool(expr,ctxt)
    if expr.op in [RE_NONE,RE_ALL,RE_ALLCHAR]:
        return typecheck_regex_consts(expr, ctxt)
    if expr.op == STR_IN_RE:
        return typecheck_str_in_re(expr,ctxt)
    if expr.op in [RE_KLENE, RE_COMP, RE_OPT, RE_PLUS]:
        return typecheck_regex_binary(expr,ctext)
    if expr.op in [RE_DIFF, RE_CONCAT, RE_UNION, RE_INTER]: 
        return typecheck_regex_binary(expr,ctext)
    if expr.op == STR_AT:
        return typecheck_str_at(expr,ctxt)
    if expr.op == STR_SUBSTR:
        return typecheck_substr(expr, ctxt)
    if expr.op == STR_INDEXOF:
        return typecheck_index_of(expr,ctxt)
    if expr.op in [STR_REPLACE, STR_REPLACE_ALL]:
        return typecheck_replace(expr,ctxt)
    if expr.op in [STR_REPLACE_RE, STR_REPLACE_RE_ALL]:
        return typecheck_replace(expr,ctxt)
    if expr.op in [STR_TO_CODE,STR_TO_INT]:
        return typecheck_str_to_int(expr,ctxt) 
    if expr.op in [STR_FROM_CODE,STR_FROM_INT]:
        return typecheck_int_to_string(expr,ctxt)
    if expr.op == STR_IS_DIGIT:
        return typecheck_is_digit(expr,ctxt)
   
def typecheck_select(expr,ctxt):
    """ 
    (select (Array X Y) X Y) 
    """
    array_type = typecheck_expr(expr.subterms[0],ctxt) 
    if isinstance(array_type, ARRAY_TYPE):
        raise TypeCheckError(expr)  
    x_type = typecheck_expr(expr.subterms[1],ctxt)
    if x_type != array_type.index_type: 
        raise TypeCheckError(expr)  
    return array_type.payload_type

def typecheck_store(expr,ctxt):
    """
    (store (Array X Y) X Y (Array X Y)))
    """
    array_type = typecheck_expr(expr.subterms[0],ctxt) 
    if isinstance(array_type, ARRAY_TYPE):
        raise TypeCheckError(expr)  
    x_type = typecheck_expr(expr.subterms[1],ctxt)
    y_type = typecheck_expr(expr.subterms[2],ctxt)
    if x_type != array_type.index_type and y_type != array_type.payload_type: 
        raise TypeCheckError(expr)  
    return array_type 

def typecheck_array_ops(expr,ctxt):
    if expr.op == SELECT: 
        return typecheck_select(expr,ctxt)
    if expr.op == STORE:
        return typecheck_store(expr,ctxt)

def typecheck_bv_concat(expr,ctxt): 
    """ 
    (concat (_ BitVec i) (_ BitVec j) (_ BitVec m)) 
    """
    arg1,arg2 = expr.subterms[0], expr.subterms[1]
    if not isinstance(arg1,BITVECTOR_TYPE) or not isinstance(arg2,BITVECTOR_TYPE):  
        raise TypeCheckError(expr)  
    bitwidth = arg1.bitwidth + arg2.bitwidth 
    return BITVECTOR_TYPE(bitwidth)

def typecheck_bv_unary(expr,ctxt):
    """
     (op1 (_ BitVec m) (_ BitVec m))
    """
    arg = expr.subterms[0]
    if not isinstance(arg,BITVECTOR_TYPE):
        raise TypeCheckError(expr)  
    return arg.type

def typecheck_bv_binary(expr,ctxt):
    """
    (op2 (_ BitVec m) (_ BitVec m) (_ BitVec m))
    """
    arg1,arg2 = expr.subterms[0], expr.subterms[1]
    if not isinstance(arg1,BITVECTOR_TYPE) or not isinstance(arg2,BITVECTOR_TYPE):  
        raise TypeCheckError(expr)  
    return BITVECTOR_TYPE(arg1.bitwidth)

def typecheck_bvult(expr,ctxt):
    """  
    (bvult (_ BitVec m) (_ BitVec m) Bool)
    """
    arg1,arg2 = expr.subterms[0], expr.subterms[1]
    if not isinstance(arg1,BITVECTOR_TYPE) or not isinstance(arg2,BITVECTOR_TYPE):  
        raise TypeCheckError(expr)  
    return BOOLEAN_TYPE

def typecheck_bv_ops(expr,ctxt):
    if expr.op == BV_CONCAT:
        return typecheck_bv_concat(expr,ctxt)
    if expr.op in [BVNOT,BVNEG]:
        return typecheck_bv_unary(expr,ctxt)
    if expr.op in [BVAND, BVOR,BVADD,BVMUL,BVUDIV,BVUREM,BVSHL,BVLSHR]:
        return typecheck_bv_binary(expr,ctxt)
    if expr.op == BVULT:
        return typecheck_bvult(expr,ctxt) 

def typecheck_fp_unary(expr, ctxt): 
    """
    (fp.abs (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
    (fp.neg (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
    """
    if not isinstance(typecheck_expr(expr.subterms[0],ctxt),FP_TYPE):
        raise TypeCheckError(expr)  
    return typecheck_expr(expr.subterms[0],ctxt)

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
    if typecheck_expr(arg1,ctxt) != ROUNDINGMODE_TYPE:
        raise TypeCheckError(expr)  
    if not isintance(typecheck_expr(arg2,ctxt),FP_TYPE) or\
       not isintance(typecheck_expr(arg3,ctxt),FP_TYPE):
        raise TypeCheckError(expr)  
    return typecheck_expr(arg2,ctxt)

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
    if not isintance(typecheck_expr(arg,ctxt),FP_TYPE):
        raise TypeCheckError(expr)  
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
    if not isintance(typecheck_expr(arg1,ctxt),FP_TYPE) or\
       not isintance(typecheck_expr(arg2,ctxt),FP_TYPE):
        raise TypeCheckError(expr)  
    return BOOLEAN_TYPE

def typecheck_fp_minmax(expr,ctxt):
    """
    (fp.min (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)) 
    (fp.max (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb))
    """
    arg1 = expr.subterms[0]  
    arg2 = expr.subterms[1]  
    if not isintance(typecheck_expr(arg1,ctxt),FP_TYPE) or\
       not isintance(typecheck_expr(arg2,ctxt),FP_TYPE):
        raise TypeCheckError(expr)
    return typecheck_expr(arg1,ctxt)

def typecheck_fp_fma(expr,ctxt):
    """
    (fp.fma RoundingMode (_ FloatingPoint eb sb) (_ FloatingPoint eb sb) (_ FloatingPoint eb sb)
     (_ FloatingPoint eb sb))
    """
    arg1 = expr.subterms[0]  
    arg2 = expr.subterms[1]  
    arg3 = expr.subterms[1]  
    if not isintance(typecheck_expr(arg1,ctxt),FP_TYPE) or\
       not isintance(typecheck_expr(arg2,ctxt),FP_TYPE) or\
       not isintance(typecheck_expr(arg3,ctxt),FP_TYPE):
        raise TypeCheckError(expr)
    return typecheck_expr(arg1,ctxt)

def typecheck_fp_ops(expr,ctxt):
    if expr.op in [FP_ABS, FP_NEG]: 
        return typecheck_fp_unary(expr,ctxt) 
    if expr.op in [FP_ADD, FP_SUB, FP_MUL, FP_DIV,FP_SQRT, FP_REM,FP_ROUND_TO_INTEGRAL]:
        return typecheck_fp_binary_arith(expr, ctxt)
    if expr.op in [FP_NORMAL, FP_ISSUBNORMAL, FP_IS_ZERO, FP_ISINFINITE, FP_ISNAN, FP_ISNEGATIVE, FP_ISPOSITIVE]:
        return typecheck_fp_unary_bool_rt(expr, ctxt)
    if expr.op in [FP_LEQ,FP_LT,FP_GEQ,FP_GT,FP.EQ]:
        return typecheck_fp_comparison(expr, ctxt) 
    if expr.op in [FP_MIN, FP_MAX]:
        return typecheck_fp_minmax(expr, ctxt) 
    if expr.op == FP_FMA: 
        return typecheck_fp_fma(expr, ctxt)

def typecheck_expr(expr, ctxt=[]):
    print("expr", expr) 
    print("type(expr)", type(expr))
    # TODO: consolidate CORE, REAL and INT 
    if expr.is_const or expr.is_var or expr.is_indexed_id:
        return expr.type
    if expr.op:
        if expr.op == NOT:
            return typecheck_not(expr,ctxt)
        if expr.op == UNARY_MINUS and len(expr.subterms) == 1:
            return typecheck_unary_minus(expr,ctxt)
        if expr.op in [MINUS, PLUS, MULTIPLY]:
            return typecheck_nary_numeral_ret(expr,ctxt)
        if expr.op in [DIV, MOD, ABS]:
            return typecheck_nary_int_ret(expr,ctxt)
        if expr.op == REAL_DIV: 
            return typecheck_real_div(expr,ctxt)
        if expr.op == MINUS: 
            return typecheck_nary_minus(expr,ctxt)
        if expr.op in EQ:
            return typecheck_eq(expr,ctxt)
        if expr.op == ITE:
            return typecheck_ite(expr,ctxt)
        if expr.op in [GT,GTE,LT,LTE]:
            return typecheck_comp_ops(expr, ctxt)
        if expr.op == TO_REAL:
            return typecheck_to_real(expr, ctxt) 
        if expr.op == TO_INT:
            return typecheck_to_int(expr, ctxt) 
        if expr.op == IS_INT:
            return typecheck_is_int(expr, ctxt) 
        if expr.op in STRING_OPS:
            return typecheck_string_ops(expr,ctxt)
        if expr.op in ARRAY_OPS:
            return typecheck_array_ops(expr,ctxt) 
        if expr.op in BV_OPS:
            return typecheck_bv_ops(expr,ctxt)
        if expr.op in FP_OPS:
            return typecheck_fp_ops(expr,ctxt)
    if expr.quantifier:     
        pass


    # TODO raise exception - type-checking failed
    # in non-strict case, just return Unknown
