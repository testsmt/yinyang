import random
import copy

from src.generators.Generator import Generator
from src.parsing.parse import *
from src.parsing.typechecker_recur import *

type2num = {'Bool': 0, 'Real': 1, 'Int': 2, 'RoundingMode': 3, 'String': 4, 
'RegLan': 5, 'Unknown': 6}

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
                exprs[0].append(i)
            elif expr_type[i] == REAL_TYPE:
                exprs[1].append(i)
            elif expr_type[i] == INTEGER_TYPE:
                exprs[2].append(i)
            elif expr_type[i] == ROUNDINGMODE_TYPE:
                exprs[3].append(i)
            elif expr_type[i] == STRING_TYPE:
                exprs[4].append(i)
            elif expr_type[i] == Regex:
                exprs[5].append(i)
            else: 
                exprs[6].append(i)
        return exprs
        
    def get_replacee(self, av_expr, expr_type):
        exprs = self.categorize(av_expr, expr_type)
        types = []
        for i in range(6):
            if len(exprs[i]) >= 2:
                types.append(i)
        if types:
            typ = random.choice(types)
            t1, t2 = random.sample(exprs[typ], 2)
            while av_expr[t1] == av_expr[t2]:
                if len(exprs[typ]) >= 3:
                    exprs[typ].remove(t2)
                    t2 = random.choice(exprs[typ])
            if av_expr[t1] != av_expr[t2]:
                return t1, t2
        return False

    def _add_seedinfo(self,formula):
        formula.commands = [Comment(self.seed_fn)] + formula.commands

    def generate(self):
        av_expr = []
        expr_type = []
        cmd = []
        for i in range(len(self.formula.assert_cmd)):
            exp, typ = typecheck_recur(self.formula.assert_cmd[i], self.ctxt)
            av_expr += exp
            expr_type += typ
            cmd += [i]*len(exp)
        res = self.get_replacee(av_expr,expr_type)
        if res:
            t1, t2 = res
            cmd1 = self.formula.assert_cmd[cmd[t1]]
            cmd2 = self.formula.assert_cmd[cmd[t2]]
            t1_copy = copy.deepcopy(av_expr[t1])
            t2_copy = copy.deepcopy(av_expr[t2])
            print("original expressions: {}, {}".format(cmd1, cmd2))
            cmd1.term.substitute(av_expr[t1], t2_copy)
            cmd2.term.substitute(av_expr[t2], t1_copy)
            print("mutated expressions:  {}, {}".format(cmd1, cmd2))
            return self._add_seedinfo(self.formula), True
        return False
