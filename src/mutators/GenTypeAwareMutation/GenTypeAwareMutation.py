import random

from src.mutators.Mutator import Mutator
from src.mutators.GenTypeAwareMutation.Operator import *
from src.mutators.GenTypeAwareMutation.util import *
from src.parsing.Parse import *
from src.parsing.Ast import Expr

class GenTypeAwareMutation(Mutator):
    def __init__(self, formula, args, unique_expr):
        self.args = args
        self.formula = formula
        self.unique_expr = unique_expr
        self.operators = []

        self.parse_config_file()

    def parse_config_file(self):
        """
        Read the customizable configuration file.
        Customize the configuration file at config/generalization.txt.
        Configuration file contains all the signatures of SMT-LIB operators
        and the signatures are used for operator choice during the mutation.
        """
        with open(self.args.config_file) as f:
            lines = f.readlines()

        for line in lines:
            line = line.strip("\n")                 # remove linebreaks
            if ";" in line:                         # ignore comments
                line = line[:line.index(";")]
            if line.strip() == "":                  # skip empty lines
                continue
            line = line.strip()                     # remove trailing whitespaces
            tokens = line.split(" ")

            if not "par" in tokens[0]:
                op_name, type_strings, attributes = handle_non_parametric_op(tokens)
                op = Operator(op_name,type_strings,attributes)
            else:
                op_name, type_strings, attributes, parameters = handle_parametric_op(tokens)
                op = Operator(op_name,type_strings,attributes,parameters)
            self.operators.append(op)

    def has_types(self,types):
        """
        types: list of types (possibly redundant)

        :returns: True if the seed formula supports the types
        """
        for t in set(types):
            if t == ALL: continue
            type_id = type2num[t]
            if len(self.unique_expr[type_id]) == 0:
                return False
        return True



    def get_candidate_ops(self,term):
        """
        term: term object

        An operator op is a candidate (op arg1 ... argk ret)
        (1) if its return type matches the type of t or has polymorphic return type
            (i.e. ret == ALL) and
        (2) if the seed formula has terms t1...tn such that tk.type = argk.type.

        :returns: a list of candidate operators
        """
        candidate_ops = []
        for op in self.operators:

            # Debugging
            #   if term.type == None:
            #     print("term=",term,"type",term.type)
            #     assert(False)

            if op.rtype != ALL and op.rtype != term.type:
                continue
            if self.has_types(op.arg_types):
                candidate_ops.append(op)
        return candidate_ops

    def get_replacee(self,term):
        """
        term: term object

        Choose randomly an operator from the list of candidate operators.

        When id is chosen for the operator, we pick an expression of a
        same type as input term. Else, we choose expression(s) according to the
        signature of the operator from the configuration file and generate a new expression.

        :returns: newly generated expression for substitution
        """
        candidate_ops = self.get_candidate_ops(term)
        op = random.choice(candidate_ops)
        args = []
        if op.name == "id":
            typ_id = type2num[term.type]
            if self.unique_expr[typ_id]:
                choices = [termPrime for termPrime in self.unique_expr[typ_id] if\
                           termPrime != term and local_compatible(term, termPrime)]

            if len(choices) == 0:
                return None
            return random.choice(choices)
        else:
            for t in op.arg_types:
                typ_id =  type2num[t]
                choices = [tPrime for tPrime in self.unique_expr[typ_id]]
                arg = random.choice(choices)
                args.append(arg)

            exp = Expr(op=op.name, subterms=args)
            exp.type = op.rtype
            return exp
        return None


    def generate(self):
        """
        Perform a generative type-aware mutation.
        In case generator could not generate valid mutant, return false.

        :returns: mutant formula, and result of mutation
        """
        success = False
        self.av_expr, self.expr_type = get_all_subterms(self.formula)
        num_holes = len(self.av_expr)
        all_holes = self.av_expr
        for _ in range(num_holes):
            t1 = random.choice(all_holes)
            t2 = self.get_replacee(t1)
            if t2:
                success = True
                t1.substitute(t1, t2)
                break
            all_holes.remove(t1)
        return self.formula, success
