import random
import copy

from src.parsing.parse import *
from src.generators.Generator import Generator
from src.generators.SemanticFusion.VariableFusion import *
from src.generators.SemanticFusion.util import *

class SemanticFusion(Generator):
    def __init__(self, seeds, args):
        super().__init__(seeds,args)
        assert(len(seeds) == 2)
        self.formula1, self.formula2 = parse_file(seeds[0],silent=False), parse_file(seeds[1], silent=False)

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


    def fuse(self, occs1, occs2, formula1, formula2, triplets):
        # Generate random variable pairs from both formulas    
        rand_var_pairs = random_tuple_list(cvars(occs1), cvars(occs2))

        # For each variable pair choose a suitable template for fusion     
        # and generate the corresponding triplet (x, y, template)
        triplets = []
        for pair in rand_var_pairs:
            x, y = pair[0], pair[1]
            template = random.choice(self.templates[x.type])
            triplets.append((x, y, template))

        # For each triplet (x, y, template) get random variable occurrences occ_x, occ_y       
        # to form triplets (occ_x, occ_y, template). Replace occ_x and occ_y from  
        # these triplets by their respective inversion functions. 
        fusion_vars = []
        fusion_constr = []
        for triplet in triplets:
            x, y, template  = triplet[0], triplet[1], triplet[2]
            occs_x = [occ for occ in occs1 if occ.name == x.name]
            occs_y = [occ for occ in occs2 if occ.name == y.name]
            rand_pairs = random_tuple_list(occs_x, occs_y)

            # Fusion step 
            for p in rand_pairs:
                occ_x, occ_y = p[0], p[1] 
                z = DeclareFun(occ_x.name+"_"+occ_y.name+"_fused","",occ_x.type)
                template = fill_template(occ_x, occ_y, template)
                occ_x.substitute(occ_x, inv_x(template))
                occ_y.substitute(occ_y, inv_y(template))
                
                fusion_vars.append(z)
                fusion_constr += fusion_contraints(template) 

        if self.oracle == "unsat":
            formula = disjunction(formula1, formula2) 
            add_fusion_constraints(formula, fusion_constr)
        else:
            formula = conjunction(formula1, formula2) 
        add_var_decls(formula, fusion_vars)
        return formula

    def generate(self):
        if self.formula1.free_var_occs == [] or self.formula2.free_var_occs == []:
            return None, False
        formula1, formula2 = copy.deepcopy(self.formula1), copy.deepcopy(self.formula2)
        formula1.prefix_vars("scr1_")
        formula2.prefix_vars("scr2_")
        occs1, occs2 = formula1.free_var_occs, formula2.free_var_occs
        triplets = random_var_occs_triplets(occs1, occs2, self.templates)

        if not triplets:
            return None, False
        fused = self.fuse(occs1, occs2, formula1, formula2, triplets)
        return fused, True