import random
import copy

from src.parsing.parse import *
from src.generators.Generator import Generator
from src.generators.SemanticFusion.VariableFusion import *
from src.generators.SemanticFusion.util import random_var_triplets, random_tuple_list, disjunction, conjunction, cvars

class SemanticFusion(Generator):
    def __init__(self, formula1, formula2, args):
        self.config_file = self.args.fusionfun
        self.oracle = self.args.oracle
        self.templates = {}
        self._parse_mrs()

        if not self.oracle:
            print("ERROR: No oracle {sat,unsat} specified")
            exit(1)

    def _parse_mrs(self):
        with open(self.config_file) as f:
            lines = f.readlines()
        started=False
        curr = []
        _mrs = []

        for l in lines:
            if ";" in l: continue
            if not l.strip(): continue
            if "begin" in l:
                started = True
                continue
            if "end" in l:
                started = False
                _mrs.append("\n".join(curr))
                curr = []
                continue
            if started:
                curr.append(l)

        for i,mr in enumerate(_mrs):
            template = parse_str(mr)
            sort = template.commands[0].sort

            if not sort in self.templates:
                self.templates[sort] = [template]
            else:
                self.templates[sort].append(template)


    def fuse(self, formula1, formula2, triplets):
        
        fusion_vars = []
        fusion_constr = []
        for triplet in triplets:
            x, y, template, var_type  = triplet[0], triplet[1], triplet[2], triplet[3]
            z = DeclareFun(x+"_"+y+"_fused","",var_type)
            fusion_vars.append(z)
            template = fill_template(x, y, template, var_type)
            fusion_constr += fusion_contraints(template,var_type)
            
            occs_x = [occ for occ in formula1.free_var_occs if occ.name == x]
            occs_y = [occ for occ in formula2.free_var_occs if occ.name == y]
            # Fusion step

            k = random.randint(0, len(occs_x))
            occs_x = random.sample(occs_x, k)
            k = random.randint(0, len(occs_y))
            occs_y = random.sample(occs_y, k)

            for occ in occs_x:
                occ.substitute(occ, inv_x(template))
            for occ in occs_y:
                occ.substitute(occ, inv_y(template))

        if self.oracle == "unsat":
            formula = disjunction(formula1, formula2)
            add_fusion_constraints(formula, fusion_constr)
        else:
            formula = conjunction(formula1, formula2)
        add_var_decls(formula, fusion_vars)

        return formula
    
    def _add_seedinfo(self,formula):
        formula.commands = [Comment(self.seed2)] + formula.commands
        formula.commands = [Comment(self.seed1)] + formula.commands
        return formula


    def generate(self):
        is_fusion = True
        if self.formula1.free_var_occs == [] and self.formula2.free_var_occs == []:
            is_fusion = False
        formula1, formula2 = copy.deepcopy(self.formula1), copy.deepcopy(self.formula2)
        formula1.prefix_vars("scr1_")
        formula2.prefix_vars("scr2_")
        triplets = random_var_triplets(formula1.global_vars, formula2.global_vars, self.templates)
        if not triplets:
            is_fusion = False
        fused = self.fuse(formula1, formula2, triplets)
        return self._add_seedinfo(fused), is_fusion
