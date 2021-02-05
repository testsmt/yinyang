import random
import copy

from src.generators.Generator import Generator
from src.parsing.parse import *
from src.parsing.typechecker_recur import *

type2num = {'Bool': 0, 'Real': 1, 'Int': 2, 'RoundingMode': 3, 'String': 4, 
'RegLan': 5, 'Unknown': 6}

class TypeMutation(Generator):
    def __init__(self, formula, args):
        self.args = args 
        self.formula = formula 

    def categorize(self, expr_type):
        # 0: Bool, 1: Real, 2: Int, 3: RoundingMode, 4: String, 5: Regex, 6: Unknown 
        exprs = [[],[],[],[],[],[],[]]
        for i in range(len(expr_type)):
            if expr_type[i] == BOOLEAN_TYPE:
                exprs[0].append(i)
            elif expr_type[i] == REAL_TYPE:
                exprs[1].append(i)
            elif expr_type[i] == INTEGER_TYPE:
                exprs[2].append(i)
            elif expr_type[i] == ROUNDINGMODE_TYPE:
                exprs[3].append(i)
            elif expr_type[i] == STRING_TYPE:
                exprs[4].append(i)
            elif expr_type[i] == REGEXP_TYPE:
                exprs[5].append(i)
            else: 
                exprs[6].append(i)
        return exprs
        
    def get_replacee(self, av_expr, expr_type):
        exprs = self.categorize(expr_type)
        types = []
        for i in range(6):
            if len(exprs[i]) >= 2:
                types.append(i)
        if len(exprs[1])>= 1 and len(exprs[2])>=1:
            types.append(7)
        if types:
            typ = random.choice(types)
            # replacing int with real 
            if typ == 7:
                t1 = random.choice(exprs[1])
                t2 = random.choice(exprs[2])
                return t1, t2, 1 
            t1, t2 = random.sample(exprs[typ], 2)
            while av_expr[t1] == av_expr[t2]:
                if len(exprs[typ]) >= 3:
                    exprs[typ].remove(t2)
                    t2 = random.choice(exprs[typ])
                else:
                    return False
            if av_expr[t1] != av_expr[t2]:
                return t1, t2, 0
        return False

    def generate(self):
        av_expr = []
        expr_type = []
        for i in range(len(self.formula.assert_cmd)):
            exps, typ = typecheck_recur(self.formula.assert_cmd[i]) 
            av_expr += exps
            expr_type += typ
        res = self.get_replacee(av_expr,expr_type)
        if res:
            t1, t2, typ = res
            if typ == 0:
                t1_copy = copy.deepcopy(av_expr[t1]) 
                t2_copy = copy.deepcopy(av_expr[t2]) 
                av_expr[t1].substitute(av_expr[t1], t2_copy)
                av_expr[t2].substitute(av_expr[t2], t1_copy)
                return self.formula, True
            elif typ == 1:
                t1_copy = copy.deepcopy(av_expr[t1])
                t2_copy = copy.deepcopy(av_expr[t2]) # redudant with if branch
                t1_int = Term(op='to_int',subterms=[t1_copy])
                t2_real = Term(op='to_real',subterms=[t2_copy])
                av_expr[t1].substitute(av_expr[t1], t2_real)
                av_expr[t2].substitute(av_expr[t2], t1_int)
                return self.formula, True          
        return None, False
