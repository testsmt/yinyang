import sys
sys.setrecursionlimit(100000)

from src.parsing.ast_visitor import *
from src.parsing.parse import *
from src.parsing.types import *

# TODO: make a difference between chainable and non-chainable ops  

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
    if not typecheck(expr,ctxt) == REAL_TYPE:
         raise TypeCheckError(expr)
    return INTEGER_TYPE

def typecheck_is_int(expr, ctxt): 
    """ (is_int Real Bool) """
    if not typecheck(expr,ctxt) == REAL_TYPE:
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
    if typecheck(expr.subterms[0],ctxt) != STRING_TYPE: 
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
        if not typecheck_expr(term, ctxt) != STRING_TYPE:
            raise TypeCheckError(expr)
    return BOOLEAN_TYPE

def typecheck_str_to_re(expr, ctxt):
    """ (str.to_re String RegLan) """  
    if typecheck(expr,ctxt) != STRING_TYPE: 
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
    if typecheck(expr,ctxt) != REGEXP_TYPE:
        raise TypeCheckError(expr)
    return BOOLEAN_TYPE

def typecheck_regex_unary(expr,ctxt):
    """
    (re.* RegLan RegLan) 
    (re.comp RegLan RegLan)
    (re.opt RegLan RegLan)
    (re.+ RegLan RegLan)
    """
    if typecheck(expr,ctxt) != REGEXP_TYPE:
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
       typecheck_expr(expr.subterms[2]) != STRING: 
        raise TypeCheckError(expr)
    return STRING_TYPE 

def typecheck_replace_re(expr,ctxt):
    """
    (str.replace_re String RegLan String String) 
    (str.replace_re_all String RegLan String String) 
    """
    if typecheck_expr(expr.subterms[0]) != STRING_TYPE or\
       typecheck_expr(expr.subterms[1]) != REGEXP_TYPE or\
       typecheck_expr(expr.subterms[2]) != STRING: 
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
    if typecheck_expr(expr.subterms[0]) != STRING_TYPE:
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
    
   
def typecheck_expr(expr, ctxt=[]):
    # print("expr", expr) 
    # print("type(expr)", type(expr))
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

    # TODO raise exception - type-checking failed
    # in non-strict case, just return Unknown
