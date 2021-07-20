# Generated from SMTLIBv2.g4 by ANTLR 4.9.2
from antlr4 import *

if __name__ is not None and "." in __name__:
    from .SMTLIBv2Parser import SMTLIBv2Parser
else:
    from SMTLIBv2Parser import SMTLIBv2Parser

# This class defines a complete listener for a parse tree produced by SMTLIBv2Parser.
class SMTLIBv2Listener(ParseTreeListener):

    # Enter a parse tree produced by SMTLIBv2Parser#start.
    def enterStart(self, ctx: SMTLIBv2Parser.StartContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#start.
    def exitStart(self, ctx: SMTLIBv2Parser.StartContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#response.
    def enterResponse(self, ctx: SMTLIBv2Parser.ResponseContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#response.
    def exitResponse(self, ctx: SMTLIBv2Parser.ResponseContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#generalReservedWord.
    def enterGeneralReservedWord(self, ctx: SMTLIBv2Parser.GeneralReservedWordContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#generalReservedWord.
    def exitGeneralReservedWord(self, ctx: SMTLIBv2Parser.GeneralReservedWordContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#simpleSymbol.
    def enterSimpleSymbol(self, ctx: SMTLIBv2Parser.SimpleSymbolContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#simpleSymbol.
    def exitSimpleSymbol(self, ctx: SMTLIBv2Parser.SimpleSymbolContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#quotedSymbol.
    def enterQuotedSymbol(self, ctx: SMTLIBv2Parser.QuotedSymbolContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#quotedSymbol.
    def exitQuotedSymbol(self, ctx: SMTLIBv2Parser.QuotedSymbolContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#predefSymbol.
    def enterPredefSymbol(self, ctx: SMTLIBv2Parser.PredefSymbolContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#predefSymbol.
    def exitPredefSymbol(self, ctx: SMTLIBv2Parser.PredefSymbolContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#predefKeyword.
    def enterPredefKeyword(self, ctx: SMTLIBv2Parser.PredefKeywordContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#predefKeyword.
    def exitPredefKeyword(self, ctx: SMTLIBv2Parser.PredefKeywordContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#symbol.
    def enterSymbol(self, ctx: SMTLIBv2Parser.SymbolContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#symbol.
    def exitSymbol(self, ctx: SMTLIBv2Parser.SymbolContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#numeral.
    def enterNumeral(self, ctx: SMTLIBv2Parser.NumeralContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#numeral.
    def exitNumeral(self, ctx: SMTLIBv2Parser.NumeralContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#decimal.
    def enterDecimal(self, ctx: SMTLIBv2Parser.DecimalContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#decimal.
    def exitDecimal(self, ctx: SMTLIBv2Parser.DecimalContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#hexadecimal.
    def enterHexadecimal(self, ctx: SMTLIBv2Parser.HexadecimalContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#hexadecimal.
    def exitHexadecimal(self, ctx: SMTLIBv2Parser.HexadecimalContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#binary.
    def enterBinary(self, ctx: SMTLIBv2Parser.BinaryContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#binary.
    def exitBinary(self, ctx: SMTLIBv2Parser.BinaryContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#string.
    def enterString(self, ctx: SMTLIBv2Parser.StringContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#string.
    def exitString(self, ctx: SMTLIBv2Parser.StringContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#reg_const.
    def enterReg_const(self, ctx: SMTLIBv2Parser.Reg_constContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#reg_const.
    def exitReg_const(self, ctx: SMTLIBv2Parser.Reg_constContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#keyword.
    def enterKeyword(self, ctx: SMTLIBv2Parser.KeywordContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#keyword.
    def exitKeyword(self, ctx: SMTLIBv2Parser.KeywordContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#spec_constant.
    def enterSpec_constant(self, ctx: SMTLIBv2Parser.Spec_constantContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#spec_constant.
    def exitSpec_constant(self, ctx: SMTLIBv2Parser.Spec_constantContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#s_expr.
    def enterS_expr(self, ctx: SMTLIBv2Parser.S_exprContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#s_expr.
    def exitS_expr(self, ctx: SMTLIBv2Parser.S_exprContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#index.
    def enterIndex(self, ctx: SMTLIBv2Parser.IndexContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#index.
    def exitIndex(self, ctx: SMTLIBv2Parser.IndexContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#identifier.
    def enterIdentifier(self, ctx: SMTLIBv2Parser.IdentifierContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#identifier.
    def exitIdentifier(self, ctx: SMTLIBv2Parser.IdentifierContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#attribute_value.
    def enterAttribute_value(self, ctx: SMTLIBv2Parser.Attribute_valueContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#attribute_value.
    def exitAttribute_value(self, ctx: SMTLIBv2Parser.Attribute_valueContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#attribute.
    def enterAttribute(self, ctx: SMTLIBv2Parser.AttributeContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#attribute.
    def exitAttribute(self, ctx: SMTLIBv2Parser.AttributeContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#sort.
    def enterSort(self, ctx: SMTLIBv2Parser.SortContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#sort.
    def exitSort(self, ctx: SMTLIBv2Parser.SortContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#qual_identifier.
    def enterQual_identifier(self, ctx: SMTLIBv2Parser.Qual_identifierContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#qual_identifier.
    def exitQual_identifier(self, ctx: SMTLIBv2Parser.Qual_identifierContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#var_binding.
    def enterVar_binding(self, ctx: SMTLIBv2Parser.Var_bindingContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#var_binding.
    def exitVar_binding(self, ctx: SMTLIBv2Parser.Var_bindingContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#sorted_var.
    def enterSorted_var(self, ctx: SMTLIBv2Parser.Sorted_varContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#sorted_var.
    def exitSorted_var(self, ctx: SMTLIBv2Parser.Sorted_varContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#pattern.
    def enterPattern(self, ctx: SMTLIBv2Parser.PatternContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#pattern.
    def exitPattern(self, ctx: SMTLIBv2Parser.PatternContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#match_case.
    def enterMatch_case(self, ctx: SMTLIBv2Parser.Match_caseContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#match_case.
    def exitMatch_case(self, ctx: SMTLIBv2Parser.Match_caseContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#term.
    def enterTerm(self, ctx: SMTLIBv2Parser.TermContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#term.
    def exitTerm(self, ctx: SMTLIBv2Parser.TermContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#sort_symbol_decl.
    def enterSort_symbol_decl(self, ctx: SMTLIBv2Parser.Sort_symbol_declContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#sort_symbol_decl.
    def exitSort_symbol_decl(self, ctx: SMTLIBv2Parser.Sort_symbol_declContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#meta_spec_constant.
    def enterMeta_spec_constant(self, ctx: SMTLIBv2Parser.Meta_spec_constantContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#meta_spec_constant.
    def exitMeta_spec_constant(self, ctx: SMTLIBv2Parser.Meta_spec_constantContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#fun_symbol_decl.
    def enterFun_symbol_decl(self, ctx: SMTLIBv2Parser.Fun_symbol_declContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#fun_symbol_decl.
    def exitFun_symbol_decl(self, ctx: SMTLIBv2Parser.Fun_symbol_declContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#par_fun_symbol_decl.
    def enterPar_fun_symbol_decl(self, ctx: SMTLIBv2Parser.Par_fun_symbol_declContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#par_fun_symbol_decl.
    def exitPar_fun_symbol_decl(self, ctx: SMTLIBv2Parser.Par_fun_symbol_declContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#theory_attribute.
    def enterTheory_attribute(self, ctx: SMTLIBv2Parser.Theory_attributeContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#theory_attribute.
    def exitTheory_attribute(self, ctx: SMTLIBv2Parser.Theory_attributeContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#theory_decl.
    def enterTheory_decl(self, ctx: SMTLIBv2Parser.Theory_declContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#theory_decl.
    def exitTheory_decl(self, ctx: SMTLIBv2Parser.Theory_declContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#logic_attribue.
    def enterLogic_attribue(self, ctx: SMTLIBv2Parser.Logic_attribueContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#logic_attribue.
    def exitLogic_attribue(self, ctx: SMTLIBv2Parser.Logic_attribueContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#logic.
    def enterLogic(self, ctx: SMTLIBv2Parser.LogicContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#logic.
    def exitLogic(self, ctx: SMTLIBv2Parser.LogicContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#sort_dec.
    def enterSort_dec(self, ctx: SMTLIBv2Parser.Sort_decContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#sort_dec.
    def exitSort_dec(self, ctx: SMTLIBv2Parser.Sort_decContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#selector_dec.
    def enterSelector_dec(self, ctx: SMTLIBv2Parser.Selector_decContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#selector_dec.
    def exitSelector_dec(self, ctx: SMTLIBv2Parser.Selector_decContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#constructor_dec.
    def enterConstructor_dec(self, ctx: SMTLIBv2Parser.Constructor_decContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#constructor_dec.
    def exitConstructor_dec(self, ctx: SMTLIBv2Parser.Constructor_decContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#datatype_dec.
    def enterDatatype_dec(self, ctx: SMTLIBv2Parser.Datatype_decContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#datatype_dec.
    def exitDatatype_dec(self, ctx: SMTLIBv2Parser.Datatype_decContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#function_dec.
    def enterFunction_dec(self, ctx: SMTLIBv2Parser.Function_decContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#function_dec.
    def exitFunction_dec(self, ctx: SMTLIBv2Parser.Function_decContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#function_def.
    def enterFunction_def(self, ctx: SMTLIBv2Parser.Function_defContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#function_def.
    def exitFunction_def(self, ctx: SMTLIBv2Parser.Function_defContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#prop_literal.
    def enterProp_literal(self, ctx: SMTLIBv2Parser.Prop_literalContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#prop_literal.
    def exitProp_literal(self, ctx: SMTLIBv2Parser.Prop_literalContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#script.
    def enterScript(self, ctx: SMTLIBv2Parser.ScriptContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#script.
    def exitScript(self, ctx: SMTLIBv2Parser.ScriptContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_assert.
    def enterCmd_assert(self, ctx: SMTLIBv2Parser.Cmd_assertContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_assert.
    def exitCmd_assert(self, ctx: SMTLIBv2Parser.Cmd_assertContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_assertSoft.
    def enterCmd_assertSoft(self, ctx: SMTLIBv2Parser.Cmd_assertSoftContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_assertSoft.
    def exitCmd_assertSoft(self, ctx: SMTLIBv2Parser.Cmd_assertSoftContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_simplify.
    def enterCmd_simplify(self, ctx: SMTLIBv2Parser.Cmd_simplifyContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_simplify.
    def exitCmd_simplify(self, ctx: SMTLIBv2Parser.Cmd_simplifyContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_checkSat.
    def enterCmd_checkSat(self, ctx: SMTLIBv2Parser.Cmd_checkSatContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_checkSat.
    def exitCmd_checkSat(self, ctx: SMTLIBv2Parser.Cmd_checkSatContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_checkSatAssuming.
    def enterCmd_checkSatAssuming(
        self, ctx: SMTLIBv2Parser.Cmd_checkSatAssumingContext
    ):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_checkSatAssuming.
    def exitCmd_checkSatAssuming(self, ctx: SMTLIBv2Parser.Cmd_checkSatAssumingContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_checkSatUsing.
    def enterCmd_checkSatUsing(self, ctx: SMTLIBv2Parser.Cmd_checkSatUsingContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_checkSatUsing.
    def exitCmd_checkSatUsing(self, ctx: SMTLIBv2Parser.Cmd_checkSatUsingContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_minimize.
    def enterCmd_minimize(self, ctx: SMTLIBv2Parser.Cmd_minimizeContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_minimize.
    def exitCmd_minimize(self, ctx: SMTLIBv2Parser.Cmd_minimizeContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_maximize.
    def enterCmd_maximize(self, ctx: SMTLIBv2Parser.Cmd_maximizeContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_maximize.
    def exitCmd_maximize(self, ctx: SMTLIBv2Parser.Cmd_maximizeContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_declareConst.
    def enterCmd_declareConst(self, ctx: SMTLIBv2Parser.Cmd_declareConstContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_declareConst.
    def exitCmd_declareConst(self, ctx: SMTLIBv2Parser.Cmd_declareConstContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_declareDatatype.
    def enterCmd_declareDatatype(self, ctx: SMTLIBv2Parser.Cmd_declareDatatypeContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_declareDatatype.
    def exitCmd_declareDatatype(self, ctx: SMTLIBv2Parser.Cmd_declareDatatypeContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_declareCodatatype.
    def enterCmd_declareCodatatype(
        self, ctx: SMTLIBv2Parser.Cmd_declareCodatatypeContext
    ):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_declareCodatatype.
    def exitCmd_declareCodatatype(
        self, ctx: SMTLIBv2Parser.Cmd_declareCodatatypeContext
    ):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_declareDatatypes.
    def enterCmd_declareDatatypes(
        self, ctx: SMTLIBv2Parser.Cmd_declareDatatypesContext
    ):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_declareDatatypes.
    def exitCmd_declareDatatypes(self, ctx: SMTLIBv2Parser.Cmd_declareDatatypesContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_declareCodatatypes.
    def enterCmd_declareCodatatypes(
        self, ctx: SMTLIBv2Parser.Cmd_declareCodatatypesContext
    ):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_declareCodatatypes.
    def exitCmd_declareCodatatypes(
        self, ctx: SMTLIBv2Parser.Cmd_declareCodatatypesContext
    ):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_declareFun.
    def enterCmd_declareFun(self, ctx: SMTLIBv2Parser.Cmd_declareFunContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_declareFun.
    def exitCmd_declareFun(self, ctx: SMTLIBv2Parser.Cmd_declareFunContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_declareSort.
    def enterCmd_declareSort(self, ctx: SMTLIBv2Parser.Cmd_declareSortContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_declareSort.
    def exitCmd_declareSort(self, ctx: SMTLIBv2Parser.Cmd_declareSortContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_define.
    def enterCmd_define(self, ctx: SMTLIBv2Parser.Cmd_defineContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_define.
    def exitCmd_define(self, ctx: SMTLIBv2Parser.Cmd_defineContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_defineFun.
    def enterCmd_defineFun(self, ctx: SMTLIBv2Parser.Cmd_defineFunContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_defineFun.
    def exitCmd_defineFun(self, ctx: SMTLIBv2Parser.Cmd_defineFunContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_defineConst.
    def enterCmd_defineConst(self, ctx: SMTLIBv2Parser.Cmd_defineConstContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_defineConst.
    def exitCmd_defineConst(self, ctx: SMTLIBv2Parser.Cmd_defineConstContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_defineFunRec.
    def enterCmd_defineFunRec(self, ctx: SMTLIBv2Parser.Cmd_defineFunRecContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_defineFunRec.
    def exitCmd_defineFunRec(self, ctx: SMTLIBv2Parser.Cmd_defineFunRecContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_defineFunsRec.
    def enterCmd_defineFunsRec(self, ctx: SMTLIBv2Parser.Cmd_defineFunsRecContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_defineFunsRec.
    def exitCmd_defineFunsRec(self, ctx: SMTLIBv2Parser.Cmd_defineFunsRecContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_defineSort.
    def enterCmd_defineSort(self, ctx: SMTLIBv2Parser.Cmd_defineSortContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_defineSort.
    def exitCmd_defineSort(self, ctx: SMTLIBv2Parser.Cmd_defineSortContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_display.
    def enterCmd_display(self, ctx: SMTLIBv2Parser.Cmd_displayContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_display.
    def exitCmd_display(self, ctx: SMTLIBv2Parser.Cmd_displayContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_echo.
    def enterCmd_echo(self, ctx: SMTLIBv2Parser.Cmd_echoContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_echo.
    def exitCmd_echo(self, ctx: SMTLIBv2Parser.Cmd_echoContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_eval.
    def enterCmd_eval(self, ctx: SMTLIBv2Parser.Cmd_evalContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_eval.
    def exitCmd_eval(self, ctx: SMTLIBv2Parser.Cmd_evalContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_exit.
    def enterCmd_exit(self, ctx: SMTLIBv2Parser.Cmd_exitContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_exit.
    def exitCmd_exit(self, ctx: SMTLIBv2Parser.Cmd_exitContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_GetObjectives.
    def enterCmd_GetObjectives(self, ctx: SMTLIBv2Parser.Cmd_GetObjectivesContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_GetObjectives.
    def exitCmd_GetObjectives(self, ctx: SMTLIBv2Parser.Cmd_GetObjectivesContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_getAssertions.
    def enterCmd_getAssertions(self, ctx: SMTLIBv2Parser.Cmd_getAssertionsContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_getAssertions.
    def exitCmd_getAssertions(self, ctx: SMTLIBv2Parser.Cmd_getAssertionsContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_getAssignment.
    def enterCmd_getAssignment(self, ctx: SMTLIBv2Parser.Cmd_getAssignmentContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_getAssignment.
    def exitCmd_getAssignment(self, ctx: SMTLIBv2Parser.Cmd_getAssignmentContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_getInfo.
    def enterCmd_getInfo(self, ctx: SMTLIBv2Parser.Cmd_getInfoContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_getInfo.
    def exitCmd_getInfo(self, ctx: SMTLIBv2Parser.Cmd_getInfoContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_getModel.
    def enterCmd_getModel(self, ctx: SMTLIBv2Parser.Cmd_getModelContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_getModel.
    def exitCmd_getModel(self, ctx: SMTLIBv2Parser.Cmd_getModelContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_blockModel.
    def enterCmd_blockModel(self, ctx: SMTLIBv2Parser.Cmd_blockModelContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_blockModel.
    def exitCmd_blockModel(self, ctx: SMTLIBv2Parser.Cmd_blockModelContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_getOption.
    def enterCmd_getOption(self, ctx: SMTLIBv2Parser.Cmd_getOptionContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_getOption.
    def exitCmd_getOption(self, ctx: SMTLIBv2Parser.Cmd_getOptionContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_getProof.
    def enterCmd_getProof(self, ctx: SMTLIBv2Parser.Cmd_getProofContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_getProof.
    def exitCmd_getProof(self, ctx: SMTLIBv2Parser.Cmd_getProofContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_getUnsatAssumptions.
    def enterCmd_getUnsatAssumptions(
        self, ctx: SMTLIBv2Parser.Cmd_getUnsatAssumptionsContext
    ):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_getUnsatAssumptions.
    def exitCmd_getUnsatAssumptions(
        self, ctx: SMTLIBv2Parser.Cmd_getUnsatAssumptionsContext
    ):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_labels.
    def enterCmd_labels(self, ctx: SMTLIBv2Parser.Cmd_labelsContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_labels.
    def exitCmd_labels(self, ctx: SMTLIBv2Parser.Cmd_labelsContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_getUnsatCore.
    def enterCmd_getUnsatCore(self, ctx: SMTLIBv2Parser.Cmd_getUnsatCoreContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_getUnsatCore.
    def exitCmd_getUnsatCore(self, ctx: SMTLIBv2Parser.Cmd_getUnsatCoreContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_getValue.
    def enterCmd_getValue(self, ctx: SMTLIBv2Parser.Cmd_getValueContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_getValue.
    def exitCmd_getValue(self, ctx: SMTLIBv2Parser.Cmd_getValueContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_pop.
    def enterCmd_pop(self, ctx: SMTLIBv2Parser.Cmd_popContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_pop.
    def exitCmd_pop(self, ctx: SMTLIBv2Parser.Cmd_popContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_poly_factor.
    def enterCmd_poly_factor(self, ctx: SMTLIBv2Parser.Cmd_poly_factorContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_poly_factor.
    def exitCmd_poly_factor(self, ctx: SMTLIBv2Parser.Cmd_poly_factorContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_push.
    def enterCmd_push(self, ctx: SMTLIBv2Parser.Cmd_pushContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_push.
    def exitCmd_push(self, ctx: SMTLIBv2Parser.Cmd_pushContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_reset.
    def enterCmd_reset(self, ctx: SMTLIBv2Parser.Cmd_resetContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_reset.
    def exitCmd_reset(self, ctx: SMTLIBv2Parser.Cmd_resetContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_resetAssertions.
    def enterCmd_resetAssertions(self, ctx: SMTLIBv2Parser.Cmd_resetAssertionsContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_resetAssertions.
    def exitCmd_resetAssertions(self, ctx: SMTLIBv2Parser.Cmd_resetAssertionsContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_setInfo.
    def enterCmd_setInfo(self, ctx: SMTLIBv2Parser.Cmd_setInfoContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_setInfo.
    def exitCmd_setInfo(self, ctx: SMTLIBv2Parser.Cmd_setInfoContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_setLogic.
    def enterCmd_setLogic(self, ctx: SMTLIBv2Parser.Cmd_setLogicContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_setLogic.
    def exitCmd_setLogic(self, ctx: SMTLIBv2Parser.Cmd_setLogicContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#cmd_setOption.
    def enterCmd_setOption(self, ctx: SMTLIBv2Parser.Cmd_setOptionContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#cmd_setOption.
    def exitCmd_setOption(self, ctx: SMTLIBv2Parser.Cmd_setOptionContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#tac_then.
    def enterTac_then(self, ctx: SMTLIBv2Parser.Tac_thenContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#tac_then.
    def exitTac_then(self, ctx: SMTLIBv2Parser.Tac_thenContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#tac_and_then.
    def enterTac_and_then(self, ctx: SMTLIBv2Parser.Tac_and_thenContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#tac_and_then.
    def exitTac_and_then(self, ctx: SMTLIBv2Parser.Tac_and_thenContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#par_then.
    def enterPar_then(self, ctx: SMTLIBv2Parser.Par_thenContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#par_then.
    def exitPar_then(self, ctx: SMTLIBv2Parser.Par_thenContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#or_else.
    def enterOr_else(self, ctx: SMTLIBv2Parser.Or_elseContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#or_else.
    def exitOr_else(self, ctx: SMTLIBv2Parser.Or_elseContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#par_or_else.
    def enterPar_or_else(self, ctx: SMTLIBv2Parser.Par_or_elseContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#par_or_else.
    def exitPar_or_else(self, ctx: SMTLIBv2Parser.Par_or_elseContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#par_or.
    def enterPar_or(self, ctx: SMTLIBv2Parser.Par_orContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#par_or.
    def exitPar_or(self, ctx: SMTLIBv2Parser.Par_orContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#tryFor.
    def enterTryFor(self, ctx: SMTLIBv2Parser.TryForContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#tryFor.
    def exitTryFor(self, ctx: SMTLIBv2Parser.TryForContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#usingParams.
    def enterUsingParams(self, ctx: SMTLIBv2Parser.UsingParamsContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#usingParams.
    def exitUsingParams(self, ctx: SMTLIBv2Parser.UsingParamsContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#tactical.
    def enterTactical(self, ctx: SMTLIBv2Parser.TacticalContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#tactical.
    def exitTactical(self, ctx: SMTLIBv2Parser.TacticalContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#command.
    def enterCommand(self, ctx: SMTLIBv2Parser.CommandContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#command.
    def exitCommand(self, ctx: SMTLIBv2Parser.CommandContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#b_value.
    def enterB_value(self, ctx: SMTLIBv2Parser.B_valueContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#b_value.
    def exitB_value(self, ctx: SMTLIBv2Parser.B_valueContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#option.
    def enterOption(self, ctx: SMTLIBv2Parser.OptionContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#option.
    def exitOption(self, ctx: SMTLIBv2Parser.OptionContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#info_flag.
    def enterInfo_flag(self, ctx: SMTLIBv2Parser.Info_flagContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#info_flag.
    def exitInfo_flag(self, ctx: SMTLIBv2Parser.Info_flagContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#error_behaviour.
    def enterError_behaviour(self, ctx: SMTLIBv2Parser.Error_behaviourContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#error_behaviour.
    def exitError_behaviour(self, ctx: SMTLIBv2Parser.Error_behaviourContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#reason_unknown.
    def enterReason_unknown(self, ctx: SMTLIBv2Parser.Reason_unknownContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#reason_unknown.
    def exitReason_unknown(self, ctx: SMTLIBv2Parser.Reason_unknownContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#model_response.
    def enterModel_response(self, ctx: SMTLIBv2Parser.Model_responseContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#model_response.
    def exitModel_response(self, ctx: SMTLIBv2Parser.Model_responseContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#info_response.
    def enterInfo_response(self, ctx: SMTLIBv2Parser.Info_responseContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#info_response.
    def exitInfo_response(self, ctx: SMTLIBv2Parser.Info_responseContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#valuation_pair.
    def enterValuation_pair(self, ctx: SMTLIBv2Parser.Valuation_pairContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#valuation_pair.
    def exitValuation_pair(self, ctx: SMTLIBv2Parser.Valuation_pairContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#t_valuation_pair.
    def enterT_valuation_pair(self, ctx: SMTLIBv2Parser.T_valuation_pairContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#t_valuation_pair.
    def exitT_valuation_pair(self, ctx: SMTLIBv2Parser.T_valuation_pairContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#check_sat_response.
    def enterCheck_sat_response(self, ctx: SMTLIBv2Parser.Check_sat_responseContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#check_sat_response.
    def exitCheck_sat_response(self, ctx: SMTLIBv2Parser.Check_sat_responseContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#echo_response.
    def enterEcho_response(self, ctx: SMTLIBv2Parser.Echo_responseContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#echo_response.
    def exitEcho_response(self, ctx: SMTLIBv2Parser.Echo_responseContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#get_assertions_response.
    def enterGet_assertions_response(
        self, ctx: SMTLIBv2Parser.Get_assertions_responseContext
    ):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#get_assertions_response.
    def exitGet_assertions_response(
        self, ctx: SMTLIBv2Parser.Get_assertions_responseContext
    ):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#get_assignment_response.
    def enterGet_assignment_response(
        self, ctx: SMTLIBv2Parser.Get_assignment_responseContext
    ):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#get_assignment_response.
    def exitGet_assignment_response(
        self, ctx: SMTLIBv2Parser.Get_assignment_responseContext
    ):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#get_info_response.
    def enterGet_info_response(self, ctx: SMTLIBv2Parser.Get_info_responseContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#get_info_response.
    def exitGet_info_response(self, ctx: SMTLIBv2Parser.Get_info_responseContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#get_model_response.
    def enterGet_model_response(self, ctx: SMTLIBv2Parser.Get_model_responseContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#get_model_response.
    def exitGet_model_response(self, ctx: SMTLIBv2Parser.Get_model_responseContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#get_option_response.
    def enterGet_option_response(self, ctx: SMTLIBv2Parser.Get_option_responseContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#get_option_response.
    def exitGet_option_response(self, ctx: SMTLIBv2Parser.Get_option_responseContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#get_proof_response.
    def enterGet_proof_response(self, ctx: SMTLIBv2Parser.Get_proof_responseContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#get_proof_response.
    def exitGet_proof_response(self, ctx: SMTLIBv2Parser.Get_proof_responseContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#get_unsat_assump_response.
    def enterGet_unsat_assump_response(
        self, ctx: SMTLIBv2Parser.Get_unsat_assump_responseContext
    ):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#get_unsat_assump_response.
    def exitGet_unsat_assump_response(
        self, ctx: SMTLIBv2Parser.Get_unsat_assump_responseContext
    ):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#get_unsat_core_response.
    def enterGet_unsat_core_response(
        self, ctx: SMTLIBv2Parser.Get_unsat_core_responseContext
    ):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#get_unsat_core_response.
    def exitGet_unsat_core_response(
        self, ctx: SMTLIBv2Parser.Get_unsat_core_responseContext
    ):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#get_value_response.
    def enterGet_value_response(self, ctx: SMTLIBv2Parser.Get_value_responseContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#get_value_response.
    def exitGet_value_response(self, ctx: SMTLIBv2Parser.Get_value_responseContext):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#specific_success_response.
    def enterSpecific_success_response(
        self, ctx: SMTLIBv2Parser.Specific_success_responseContext
    ):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#specific_success_response.
    def exitSpecific_success_response(
        self, ctx: SMTLIBv2Parser.Specific_success_responseContext
    ):
        pass

    # Enter a parse tree produced by SMTLIBv2Parser#general_response.
    def enterGeneral_response(self, ctx: SMTLIBv2Parser.General_responseContext):
        pass

    # Exit a parse tree produced by SMTLIBv2Parser#general_response.
    def exitGeneral_response(self, ctx: SMTLIBv2Parser.General_responseContext):
        pass


del SMTLIBv2Parser
