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
# The above copyright notice and this permission notice shall be included in all
# copies or substantial portions of the Software.
#
# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
# IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
# FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
# AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
# LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
# OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
# SOFTWARE.

# Generated from SMTLIBv2.g4 by ANTLR 4.8
from antlr4 import *
from src.parsing.Ast import *
from src.parsing.SMTLIBv2Parser import SMTLIBv2Parser

# This class defines a complete generic visitor for a parse tree produced by SMTLIBv2Parser.
class SMTLIBv2Visitor(ParseTreeVisitor):
    # Visit a parse tree produced by SMTLIBv2Parser#response.
    def visitResponse(self, ctx: SMTLIBv2Parser.ResponseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#generalReservedWord.
    def visitGeneralReservedWord(self, ctx: SMTLIBv2Parser.GeneralReservedWordContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#simpleSymbol.
    def visitSimpleSymbol(self, ctx: SMTLIBv2Parser.SimpleSymbolContext):
        return ctx.getText()

    # Visit a parse tree produced by SMTLIBv2Parser#quotedSymbol.
    def visitQuotedSymbol(self, ctx: SMTLIBv2Parser.QuotedSymbolContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#predefSymbol.
    def visitPredefSymbol(self, ctx: SMTLIBv2Parser.PredefSymbolContext):
        return ctx.getText()

    # Visit a parse tree produced by SMTLIBv2Parser#predefKeyword.
    def visitPredefKeyword(self, ctx: SMTLIBv2Parser.PredefKeywordContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#symbol.
    def visitSymbol(self, ctx: SMTLIBv2Parser.SymbolContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#numeral.
    def visitNumeral(self, ctx: SMTLIBv2Parser.NumeralContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#decimal.
    def visitDecimal(self, ctx: SMTLIBv2Parser.DecimalContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#hexadecimal.
    def visitHexadecimal(self, ctx: SMTLIBv2Parser.HexadecimalContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#binary.
    def visitBinary(self, ctx: SMTLIBv2Parser.BinaryContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#string.
    def visitString(self, ctx: SMTLIBv2Parser.StringContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#keyword.
    def visitKeyword(self, ctx: SMTLIBv2Parser.KeywordContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#spec_constant.
    def visitSpec_constant(self, ctx: SMTLIBv2Parser.Spec_constantContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#s_expr.
    def visitS_expr(self, ctx: SMTLIBv2Parser.S_exprContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#index.
    def visitIndex(self, ctx: SMTLIBv2Parser.IndexContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#identifier.
    def visitIdentifier(self, ctx: SMTLIBv2Parser.IdentifierContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#attribute_value.
    def visitAttribute_value(self, ctx: SMTLIBv2Parser.Attribute_valueContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#attribute.
    def visitAttribute(self, ctx: SMTLIBv2Parser.AttributeContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#qual_identifier.
    def visitQual_identifier(self, ctx: SMTLIBv2Parser.Qual_identifierContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#var_binding.
    def visitVar_binding(self, ctx: SMTLIBv2Parser.Var_bindingContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#sorted_var.
    def visitSorted_var(self, ctx: SMTLIBv2Parser.Sorted_varContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#pattern.
    def visitPattern(self, ctx: SMTLIBv2Parser.PatternContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#match_case.
    def visitMatch_case(self, ctx: SMTLIBv2Parser.Match_caseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#sort_symbol_decl.
    def visitSort_symbol_decl(self, ctx: SMTLIBv2Parser.Sort_symbol_declContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#meta_spec_constant.
    def visitMeta_spec_constant(self, ctx: SMTLIBv2Parser.Meta_spec_constantContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#fun_symbol_decl.
    def visitFun_symbol_decl(self, ctx: SMTLIBv2Parser.Fun_symbol_declContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#par_fun_symbol_decl.
    def visitPar_fun_symbol_decl(self, ctx: SMTLIBv2Parser.Par_fun_symbol_declContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#theory_attribute.
    def visitTheory_attribute(self, ctx: SMTLIBv2Parser.Theory_attributeContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#theory_decl.
    def visitTheory_decl(self, ctx: SMTLIBv2Parser.Theory_declContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#logic_attribue.
    def visitLogic_attribue(self, ctx: SMTLIBv2Parser.Logic_attribueContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#logic.
    def visitLogic(self, ctx: SMTLIBv2Parser.LogicContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#sort_dec.
    def visitSort_dec(self, ctx: SMTLIBv2Parser.Sort_decContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#selector_dec.
    def visitSelector_dec(self, ctx: SMTLIBv2Parser.Selector_decContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#constructor_dec.
    def visitConstructor_dec(self, ctx: SMTLIBv2Parser.Constructor_decContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#datatype_dec.
    def visitDatatype_dec(self, ctx: SMTLIBv2Parser.Datatype_decContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#function_dec.
    def visitFunction_dec(self, ctx: SMTLIBv2Parser.Function_decContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#function_def.
    def visitFunction_def(self, ctx: SMTLIBv2Parser.Function_defContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#prop_literal.
    def visitProp_literal(self, ctx: SMTLIBv2Parser.Prop_literalContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_assert.
    def visitCmd_assert(self, ctx: SMTLIBv2Parser.Cmd_assertContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_checkSat.
    def visitCmd_checkSat(self, ctx: SMTLIBv2Parser.Cmd_checkSatContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_checkSatAssuming.
    def visitCmd_checkSatAssuming(
        self, ctx: SMTLIBv2Parser.Cmd_checkSatAssumingContext
    ):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_declareConst.
    def visitCmd_declareConst(self, ctx: SMTLIBv2Parser.Cmd_declareConstContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_declareDatatype.
    def visitCmd_declareDatatype(self, ctx: SMTLIBv2Parser.Cmd_declareDatatypeContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_declareDatatypes.
    def visitCmd_declareDatatypes(
        self, ctx: SMTLIBv2Parser.Cmd_declareDatatypesContext
    ):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_declareFun.
    def visitCmd_declareFun(self, ctx: SMTLIBv2Parser.Cmd_declareFunContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_declareSort.
    def visitCmd_declareSort(self, ctx: SMTLIBv2Parser.Cmd_declareSortContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_defineFun.
    def visitCmd_defineFun(self, ctx: SMTLIBv2Parser.Cmd_defineFunContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_defineFunRec.
    def visitCmd_defineFunRec(self, ctx: SMTLIBv2Parser.Cmd_defineFunRecContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_defineFunsRec.
    def visitCmd_defineFunsRec(self, ctx: SMTLIBv2Parser.Cmd_defineFunsRecContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_defineSort.
    def visitCmd_defineSort(self, ctx: SMTLIBv2Parser.Cmd_defineSortContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_echo.
    def visitCmd_echo(self, ctx: SMTLIBv2Parser.Cmd_echoContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_exit.
    def visitCmd_exit(self, ctx: SMTLIBv2Parser.Cmd_exitContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_getAssertions.
    def visitCmd_getAssertions(self, ctx: SMTLIBv2Parser.Cmd_getAssertionsContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_getAssignment.
    def visitCmd_getAssignment(self, ctx: SMTLIBv2Parser.Cmd_getAssignmentContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_getInfo.
    def visitCmd_getInfo(self, ctx: SMTLIBv2Parser.Cmd_getInfoContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_getModel.
    def visitCmd_getModel(self, ctx: SMTLIBv2Parser.Cmd_getModelContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_getOption.
    def visitCmd_getOption(self, ctx: SMTLIBv2Parser.Cmd_getOptionContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_getProof.
    def visitCmd_getProof(self, ctx: SMTLIBv2Parser.Cmd_getProofContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_getUnsatAssumptions.
    def visitCmd_getUnsatAssumptions(
        self, ctx: SMTLIBv2Parser.Cmd_getUnsatAssumptionsContext
    ):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_getUnsatCore.
    def visitCmd_getUnsatCore(self, ctx: SMTLIBv2Parser.Cmd_getUnsatCoreContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_getValue.
    def visitCmd_getValue(self, ctx: SMTLIBv2Parser.Cmd_getValueContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_pop.
    def visitCmd_pop(self, ctx: SMTLIBv2Parser.Cmd_popContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_push.
    def visitCmd_push(self, ctx: SMTLIBv2Parser.Cmd_pushContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_reset.
    def visitCmd_reset(self, ctx: SMTLIBv2Parser.Cmd_resetContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_resetAssertions.
    def visitCmd_resetAssertions(self, ctx: SMTLIBv2Parser.Cmd_resetAssertionsContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_setInfo.
    def visitCmd_setInfo(self, ctx: SMTLIBv2Parser.Cmd_setInfoContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_setLogic.
    def visitCmd_setLogic(self, ctx: SMTLIBv2Parser.Cmd_setLogicContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#cmd_setOption.
    def visitCmd_setOption(self, ctx: SMTLIBv2Parser.Cmd_setOptionContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#b_value.
    def visitB_value(self, ctx: SMTLIBv2Parser.B_valueContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#option.
    def visitOption(self, ctx: SMTLIBv2Parser.OptionContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#info_flag.
    def visitInfo_flag(self, ctx: SMTLIBv2Parser.Info_flagContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#error_behaviour.
    def visitError_behaviour(self, ctx: SMTLIBv2Parser.Error_behaviourContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#reason_unknown.
    def visitReason_unknown(self, ctx: SMTLIBv2Parser.Reason_unknownContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#model_response.
    def visitModel_response(self, ctx: SMTLIBv2Parser.Model_responseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#info_response.
    def visitInfo_response(self, ctx: SMTLIBv2Parser.Info_responseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#valuation_pair.
    def visitValuation_pair(self, ctx: SMTLIBv2Parser.Valuation_pairContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#t_valuation_pair.
    def visitT_valuation_pair(self, ctx: SMTLIBv2Parser.T_valuation_pairContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#check_sat_response.
    def visitCheck_sat_response(self, ctx: SMTLIBv2Parser.Check_sat_responseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#echo_response.
    def visitEcho_response(self, ctx: SMTLIBv2Parser.Echo_responseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#get_assertions_response.
    def visitGet_assertions_response(
        self, ctx: SMTLIBv2Parser.Get_assertions_responseContext
    ):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#get_assignment_response.
    def visitGet_assignment_response(
        self, ctx: SMTLIBv2Parser.Get_assignment_responseContext
    ):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#get_info_response.
    def visitGet_info_response(self, ctx: SMTLIBv2Parser.Get_info_responseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#get_model_response.
    def visitGet_model_response(self, ctx: SMTLIBv2Parser.Get_model_responseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#get_option_response.
    def visitGet_option_response(self, ctx: SMTLIBv2Parser.Get_option_responseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#get_proof_response.
    def visitGet_proof_response(self, ctx: SMTLIBv2Parser.Get_proof_responseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#get_unsat_assump_response.
    def visitGet_unsat_assump_response(
        self, ctx: SMTLIBv2Parser.Get_unsat_assump_responseContext
    ):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#get_unsat_core_response.
    def visitGet_unsat_core_response(
        self, ctx: SMTLIBv2Parser.Get_unsat_core_responseContext
    ):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#get_value_response.
    def visitGet_value_response(self, ctx: SMTLIBv2Parser.Get_value_responseContext):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#specific_success_response.
    def visitSpecific_success_response(
        self, ctx: SMTLIBv2Parser.Specific_success_responseContext
    ):
        return self.visitChildren(ctx)

    # Visit a parse tree produced by SMTLIBv2Parser#general_response.
    def visitGeneral_response(self, ctx: SMTLIBv2Parser.General_responseContext):
        return self.visitChildren(ctx)


del SMTLIBv2Parser
