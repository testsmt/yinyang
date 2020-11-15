import random 
import copy 
import re

from src.generators.Generator import Generator
from src.generators.SemanticFusion.parsing import *

class SemanticFusion(Generator): 

    def __init__(self, seeds, args): 
        super().__init__(seeds)
        assert(len(seeds) == 2)
        self.args = args
        self.formula1, self.formula2 = seeds[0], seeds[1]

        if self.args.oracle == "unknown": 
            exit("Must set oracle for semantic fusion (using -o).")


    def generate(self):

        script1 = get_script_from_file(self.formula1)
        script2 = get_script_from_file(self.formula2)

        shifted_script1 = shift_script(script1, "shifted1_")
        shifted_script2 = shift_script(script2, "shifted2_")

        symbols1 = get_symbols(shifted_script1, only_zero_valued_funcs=True)
        symbols2 = get_symbols(shifted_script2, only_zero_valued_funcs=True)

        metamophic_tuples = random_map(symbols1, symbols2)
        mutant = self.__fuse(shifted_script1, shifted_script2, metamophic_tuples)
        testcase = "%s/%s.smt2" % (self.args.scratchfolder, self.args.name)
        string2file(testcase, mutant)
        
        return testcase
    
    def __fuse(self, script1, script2, metamorphic_tuples):
            
        logic1, sorts1, consts1, decl_funcs1, def_funcs1, asserts1 = decompose(script1)
        logic2, sorts2, consts2, decl_funcs2, def_funcs2, asserts2 = decompose(script2)

        script1_declare_text = "".join(consts1+decl_funcs1+def_funcs1)
        script2_declare_text = "".join(consts2+decl_funcs2+def_funcs2)
        script1_assert_text = "".join(asserts1)
        script2_assert_text = "".join(asserts2)
        sorts = list(set(sorts1).union(set(sorts2)))
        logic = "(set-logic ALL)"

        # synthesis declares
        declare_text = ""
        declare_text += "".join(sorts)
        for metamorphic_tuple in metamorphic_tuples:
            declare_text = declare_text + metamorphic_tuple.get_z_declaration()
        declare_text += script1_declare_text
        declare_text += script2_declare_text

        # substitute script1
        for metamorphic_tuple in metamorphic_tuples:
            script1_assert_text = replace_variable(
                script1_assert_text,
                metamorphic_tuple.first_var.name,
                metamorphic_tuple.get_x_substituent(),
                50)
            # substitute script2
        for metamorphic_tuple in metamorphic_tuples:
            script2_assert_text = replace_variable(
                script2_assert_text,
                metamorphic_tuple.second_var.name,
                metamorphic_tuple.get_y_substituent(),
                50)

        # disjoin or conjoin the formulae
        if self.args.oracle == "unsat":
            mutant = disjunction(script1_assert_text, script2_assert_text)
            _, _, _, _,_, mutant_asserts = decompose(mutant)
            script_text = logic +  declare_text + "".join(mutant_asserts)
        else:
            assert_text = script1_assert_text + script2_assert_text
            _,_,_,_,_,asserts = decompose(assert_text)
            random.shuffle(asserts)
            assert_text = "".join(asserts)
            script_text = logic + declare_text + assert_text

        if self.args.oracle == "unsat":
            for metamorphic_tuple in metamorphic_tuples:
                new_line = metamorphic_tuple.get_xy_constraints()
                script_text = script_text + new_line

        script_text = script_text + "(check-sat)"
        script_text = script_text + "(exit)"

        #clean :named
        script_text = re.sub(r"\:named\ \w*\)", "", script_text)
        script_text = script_text.replace("(!","")

        return script_text
