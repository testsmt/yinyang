import random
import copy

from src.generators.Generator import Generator
from src.parsing.parse import *
from src.parsing.typechecker_recur import *

class TypeMutation(Generator):
    # two mutation strategies
    # first, within the single expression
    # second, with two expressions(possible mutation happens within the single expression)
    def __init__(self, seed_fns, args, ctxt):
        assert(len(seed_fns) == 1)
        self.seed_fn = seed_fns[0]
        self.args = args 
        self.formula, _ = parse_file(seed_fns[0])
        self.ctxt = ctxt

    def categorize(self, av_expr, expr_type):
        # 0: Bool, 1: Real, 2: Int, 3: RoundingMode, 4: String, 5: Regex, 6: Unknown 
        exprs = [[],[],[],[],[],[],[]]
        for i in range(len(av_expr)):
            if expr_type[i] == BOOLEAN_TYPE:
                exprs[0].append(av_expr[i])
            elif expr_type[i] == REAL_TYPE:
                exprs[1].append(av_expr[i])
            elif expr_type[i] == INTEGER_TYPE:
                exprs[2].append(av_expr[i])
            elif expr_type[i] == ROUNDINGMODE_TYPE:
                exprs[3].append(av_expr[i])
            elif expr_type[i] == STRING_TYPE:
                exprs[4].append(av_expr[i])
            elif expr_type[i] == Regex:
                exprs[5].append(av_expr[i])
            else: 
                exprs[6].append(av_expr[i])
        return exprs

    def get_replacee_single_expression(self, cmd):
        av_expr, expr_type = typecheck_recur_list(cmd, self.ctxt)
        exprs = self.categorize(av_expr, expr_type)
        types = []
        for i in range(6):
            if len(exprs[i]) >= 2:
                types.append(i)
        if types:
            typ = random.choice(types)
            t1, t2 = random.sample(exprs[typ],2)
            return t1, t2
        return False
        
    def get_replacee(self, cmd1, cmd2):
        av_expr1, expr_type1 = typecheck_recur_list(cmd1, self.ctxt)
        av_expr2, expr_type2 = typecheck_recur_list(cmd2, self.ctxt)
        exprs1 = self.categorize(av_expr1, expr_type1)
        exprs2 = self.categorize(av_expr2, expr_type2)
        types = []
        for i in range(6):
            if len(exprs1[i]) >= 1 and len(exprs2[i]) >= 1:
                types.append(i)
        if types:
            typ = random.choice(types)
            t1 = random.choice(exprs1[typ])
            t2 = random.choice(exprs2[typ])
            return t1, t2
        return False

    def _add_seedinfo(self,formula):
        formula.commands = [Comment(self.seed_fn)] + formula.commands

    def generate_single_expression(self):
        cmd = random.choice(self.formula.assert_cmd)
        print("original expression: {}".format(cmd))
        res = self.get_replacee_single_expression(cmd)
        if res:
            t1, t2 = res
            t1_copy = copy.deepcopy(t1)
            t2_copy = copy.deepcopy(t2)
            cmd.term.substitute(t1, t2_copy)
            cmd.term.substitute(t2, t1_copy)
            print("mutated expression:  {}".format(cmd))
            return self._add_seedinfo(self.formula), True
        return False 

    def generate(self):
        cmd1 = random.choice(self.formula.assert_cmd)
        cmd2 = random.choice(self.formula.assert_cmd)
        print("original expressions: {}, {}".format(cmd1, cmd2))
        res = self.get_replacee(cmd1,cmd2)
        if res:
            t1, t2 = res
            t1_copy = copy.deepcopy(t1)
            t2_copy = copy.deepcopy(t2)
            cmd1.term.substitute(t1, t2_copy)
            cmd2.term.substitute(t2, t1_copy)
            print("mutated expressions:  {}, {}".format(cmd1, cmd2))
            return self._add_seedinfo(self.formula), True
        return False
