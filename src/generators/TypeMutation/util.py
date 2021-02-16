import copy

from src.parsing.ast import Term
from src.parsing.types import * 

type2num = {
    'Bool': 0, 
    'Real': 1, 
    'Int': 2, 
    'RoundingMode': 3, 
    'String': 4, 
    'RegLan': 5, 
    'Unknown': 6
}

def get_subterms(expr):
    """
    Get all subexpression of term object expr. 
    :returns: av_expr list of expressions 
              expr_types list of types 
              (s.t. expression e = av_expr[i] has type expr_types[i]) 
    """
    av_expr = []
    expr_types = []
    if isinstance(expr, Term):
        if expr.subterms:
            for s in expr.subterms:
                new_av, new_type = get_subterms(s)
                av_expr += new_av
                expr_types += new_type
            new_type = expr.type 
            expr_types.append(new_type)
            av_expr.append(expr)
        else:
            av_expr.append(expr)
            expr_types.append(expr.type)
    else:
        if expr.term:
            new_av, new_type = get_subterms(expr.term)
            av_expr += new_av
            expr_types += new_type
    return av_expr, expr_types


def get_all_subterms(formula):
    """
    Get all expressions within a formula and their types. 
    :returns: av_expr list of expressions 
              expr_types list of types 
              (s.t. expression e = av_expr[i] has type expr_types[i]) 
    """
    av_expr = []
    expr_type = []
    for i in range(len(formula.assert_cmd)):
        exps, typ = get_subterms(formula.assert_cmd[i]) 
        av_expr += exps
        expr_type += typ
    return av_expr,expr_type 


def get_unique_subterms(formula):
    av_expr, expr_type = get_all_subterms(formula) 

    # 0: Bool, 1: Real, 2: Int, 3: RoundingMode, 4: String, 5: Regex, 6: Unknown 
    unique_expr = [[],[],[],[],[],[]]
    for i in range(len(expr_type)):
        if expr_type[i] == BOOLEAN_TYPE:
            unique_expr[0].append(copy.deepcopy(av_expr[i]))
        elif expr_type[i] == REAL_TYPE:
            unique_expr[1].append(copy.deepcopy(av_expr[i]))
        elif expr_type[i] == INTEGER_TYPE:
            unique_expr[2].append(copy.deepcopy(av_expr[i]))
        elif expr_type[i] == ROUNDINGMODE_TYPE:
            unique_expr[3].append(copy.deepcopy(av_expr[i]))
        elif expr_type[i] == STRING_TYPE:
            unique_expr[4].append(copy.deepcopy(av_expr[i]))
        elif expr_type[i] == REGEXP_TYPE:
            unique_expr[5].append(copy.deepcopy(av_expr[i]))

    for i in range(6):
        if unique_expr[i]:
            temp = []
            temp.append(unique_expr[i][0])
            for j in range(1,len(unique_expr[i])):
                flag = 0
                for exp in temp:
                    if unique_expr[i][j] == exp:
                        flag = 1
                        pass
                if flag == 0:
                    temp.append(unique_expr[i][j])                                
            unique_expr[i] = temp
    return unique_expr  
