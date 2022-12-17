# MIT License
#
# Copyright (c) [2020 - 2021] The yinyang authors
#
# Permission is hereby granted, free of charge, to any person obtaining a copy
# of this software and associated documentation files (the "Software"), to deal
# in the Software without restriction, including without limitation the rights
# to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
# copies of the Software, and to permit persons to whom the Software is
# furnished to do so, subject to the following conditions:
#
# The above copyright notice and this permission notice shall be included in
# all copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

import random
import copy

from yinyang.src.mutators.Mutator import Mutator
from yinyang.src.mutators.SemanticFusion.VariableFusion import (
    fill_template,
    get_z_idx,
    inv_by_name,
    fusion_contraints,
    add_fusion_constraints,
    add_var_decls,
    canonicalize_script,
    z_sort
)
from yinyang.src.mutators.SemanticFusion.Util import (
    generate_fusion_function_templates,
    populate_template_map,
    random_var_triplets,
    disjunction,
    conjunction,
)
from yinyang.src.base.Exitcodes import ERR_USAGE
from yinyang.src.parsing.Parse import parse_str
from yinyang.src.parsing.Ast import DeclareFun


class SemanticFusion(Mutator):
    def __init__(self, formula1, formula2, args):
        self.formula1 = canonicalize_script(formula1)
        self.formula2 = canonicalize_script(formula2)
        self.args = args
        self.config = self.args.config
        self.generate_functions = self.args.generate_functions > 0
        self.generate_functions_size = self.args.generate_functions
        self.multiple_variables = self.args.multiple_variables
        self.oracle = self.args.oracle
        self.templates = {}
        if not self.generate_functions:
            self._parse_mrs()

        if not self.oracle:
            print("error: No oracle {sat,unsat} specified")
            exit(ERR_USAGE)

    def _parse_mrs(self):
        with open(self.config) as f:
            lines = f.readlines()
        started = False
        curr = []
        _mrs = []

        for line in lines:
            if ";" in line:
                continue
            if not line.strip():
                continue
            if "begin" in line:
                started = True
                continue
            if "end" in line:
                started = False
                _mrs.append("\n".join(curr))
                curr = []
                continue
            if started:
                curr.append(line)

        for _, mr in enumerate(_mrs):
            template, _ = parse_str(mr)
            if (get_z_idx(template) != self.multiple_variables):
                continue
            populate_template_map(self.templates, template)

    def fuse(self, formula1, formula2, triplets):
        fusion_vars = []
        fusion_constr = []
        for triplet in triplets:
            # xs and ys map variables names to template variable declarations.
            mapped_var1, mapped_var2, template =\
                triplet[0], triplet[1], triplet[2]
            z_name = "_".join(list(mapped_var1.keys()) +
                              list(mapped_var2.keys()) + ["fused"])
            z = DeclareFun(z_name, "", z_sort(template))
            fusion_vars.append(z)
            template = fill_template(
                mapped_var1, mapped_var2, z_name, template)
            # Should I look at both input and output sorts?
            fusion_constr += fusion_contraints(template, z_sort(template))

            def _random_substitute(formula, mapped_vars, formula_var_name):
                occs = [occ for occ in formula.free_var_occs
                        if occ.name == formula_var_name]
                k = random.randint(0, len(occs))
                occs = random.sample(occs, k)
                for occ in occs:
                    occ.substitute(occ, inv_by_name(
                        template, mapped_vars[formula_var_name].symbol))
            for formula1_var_name in mapped_var1:
                _random_substitute(formula1, mapped_var1, formula1_var_name)
            for formula2_var_name in mapped_var2:
                _random_substitute(formula2, mapped_var2, formula2_var_name)

        if self.oracle == "unsat":
            formula = disjunction(formula1, formula2)
            add_fusion_constraints(formula, fusion_constr)
        else:
            formula = conjunction(formula1, formula2)
        add_var_decls(formula, fusion_vars)
        print(formula)
        return formula

    def mutate(self):
        skip_seed = False
        if self.formula1.free_var_occs == [] and\
           self.formula2.free_var_occs == []:
            skip_seed = True

        formula1, formula2 =\
            copy.deepcopy(self.formula1), copy.deepcopy(self.formula2)
        formula1.prefix_vars("scr1_")
        formula2.prefix_vars("scr2_")

        templates = generate_fusion_function_templates(
            formula1.global_vars,
            formula2.global_vars,
            self.multiple_variables,
            self.generate_functions_size
        ) \
            if self.generate_functions \
            else self.templates

        triplets = random_var_triplets(
            formula1.global_vars,
            formula2.global_vars,
            templates
        )
        fused = self.fuse(formula1, formula2, triplets)
        return fused, True, skip_seed
