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

from yinyang.src.parsing.SMTLIBv2Parser import SMTLIBv2Parser
from yinyang.src.parsing.SMTLIBv2Visitor import SMTLIBv2Visitor
from yinyang.src.parsing.Ast import (
    Var,
    Const,
    Expr,
    Quantifier,
    LabeledTerm,
    LetBinding,
    Maximize,
    Minimize,
    Pop,
    Push,
    DeclareConst,
    DeclareFun,
    Define,
    DefineFun,
    DefineFunRec,
    DefineFunsRec,
    DefineConst,
    Script,
    AssertSoft,
    Assert,
    CheckSat,
    CheckSatAssuming,
    Simplify,
    Display,
    Eval,
    GetValue,
    FunDecl,
    SMTLIBCommand,
)
from yinyang.src.parsing.Types import (
    BITVECTOR_TYPE,
    FP_TYPE,
    FUNCTION_TYPE,
    INTEGER_TYPE,
    REAL_TYPE,
    STRING_TYPE,
    BOOLEAN_TYPE,
    REGEXP_TYPE,
    ROUNDINGMODE_TYPE,
    ROUNDING_MODES,
    FP_INDEXED_CONSTANTS,
    sort2type,
)


class AstException(Exception):
    pass


class AstVisitor(SMTLIBv2Visitor):
    def __init__(self, strict=True):
        self.strict = strict
        self.global_vars = {}
        self.sorts = {}  # sort aliases from define-sort
        self.constants = {}  # nullary datatype constructors and their sort

    def visitStart(self, ctx: SMTLIBv2Parser.StartContext):
        return self.visitScript(ctx.script())

    def visitScript(self, ctx: SMTLIBv2Parser.ScriptContext):
        cmds = []
        for c in ctx.command():
            cmds.append(self.visitCommand(c))
        return Script(cmds, self.global_vars)

    def add_to_globals(self, identifier, input_sorts, output_sort):
        """
        Add a declared or defined symbol to the global variables, with its
        type for constants and a FUNCTION_TYPE for functions.

        input_sorts: list of the argument sorts
        """
        if len(input_sorts) == 0:
            self.global_vars[identifier] = sort2type(output_sort)
        else:
            self.global_vars[identifier] = FUNCTION_TYPE(
                [sort2type(sort) for sort in input_sorts],
                sort2type(output_sort)
            )

    def visitSorted_vars(self, sorted_var_ctxs):
        """
        :returns: list of the (symbol, sort) pairs and dict of their types
        """
        params = [
            (self.visitSymbol(var.symbol()), self.visitSort(var.sort()))
            for var in sorted_var_ctxs
        ]
        return params, {symbol: sort2type(sort) for symbol, sort in params}

    def add_datatypes(self, names, datatype_decs):
        """
        Add the constructors, selectors and testers of the datatypes to the
        global variables. Nullary constructors are constants. Parametric
        datatypes are not supported.
        """
        for name, dec in zip(names, datatype_decs):
            if name is None or dec.GRW_Par():
                continue
            for cons in dec.constructor_dec():
                cons_name = self.visitSymbol(cons.symbol())
                selectors = [
                    (self.visitSymbol(sel.symbol()),
                     self.visitSort(sel.sort()))
                    for sel in cons.selector_dec()
                ]
                if selectors:
                    self.add_to_globals(
                        cons_name, [sort for _, sort in selectors], name
                    )
                else:
                    self.constants[cons_name] = name
                for sel_name, sort in selectors:
                    self.add_to_globals(sel_name, [name], sort)
                for tester in ["(_ is " + cons_name + ")", "is-" + cons_name]:
                    self.add_to_globals(tester, [name], BOOLEAN_TYPE)

    def handleCommand(self, ctx: SMTLIBv2Parser.CommandContext):
        if ctx.cmd_assert():
            return Assert(self.visitTerm(ctx.term()[0], {}))
        if ctx.cmd_assertSoft():
            attr = []
            for a in ctx.attribute():
                a = self.visitAttribute(a)
                attr.append(a)
            return AssertSoft(self.visitTerm(ctx.term()[0], {}), attr)
        if ctx.cmd_simplify():
            attr = []
            for a in ctx.attribute():
                a = self.visitAttribute(a)
                attr.append(a)
            return Simplify(self.visitTerm(ctx.term()[0], {}), attr)
        if ctx.cmd_minimize():
            return Minimize(self.visitTerm(ctx.term()[0], {}))
        if ctx.cmd_maximize():
            return Maximize(self.visitTerm(ctx.term()[0], {}))
        if ctx.cmd_display():
            return Display(self.visitTerm(ctx.term()[0], {}))
        if ctx.cmd_eval():
            return Eval(self.visitTerm(ctx.term()[0], {}))
        if ctx.cmd_declareConst():
            var = self.visitSymbol(ctx.symbol()[0])
            sort = self.visitSort(ctx.sort()[0])
            self.add_to_globals(var, [], sort)
            return DeclareConst(var, sort2type(sort))
        if ctx.cmd_declareFun():
            input_sorts = []
            for sort in ctx.sort()[:-1]:
                input_sorts.append(self.visitSort(sort))
            output_sort = self.visitSort(ctx.sort()[-1])
            identifier = self.visitSymbol(ctx.symbol()[0])
            self.add_to_globals(identifier, input_sorts, output_sort)
            return DeclareFun(identifier, " ".join(input_sorts), output_sort)

        # Declarations that are printed as they are, after recording the
        # symbols and sorts they declare.
        if ctx.cmd_declareDatatypes():
            names = [self.visitSymbol(dec.symbol()) for dec in ctx.sort_dec()]
            arities = [dec.numeral().getText() for dec in ctx.sort_dec()]
            names = [n if a == "0" else None for n, a in zip(names, arities)]
            self.add_datatypes(names, ctx.datatype_dec())
            return None
        if ctx.cmd_declareDatatype():
            self.add_datatypes(
                [self.visitSymbol(ctx.symbol()[0])], ctx.datatype_dec()
            )
            return None
        if ctx.cmd_defineSort() and len(ctx.symbol()) == 1:
            self.sorts[self.visitSymbol(ctx.symbol()[0])] = \
                self.visitSort(ctx.sort()[0])
            return None

        if ctx.cmd_define():
            return Define(
                self.visitSymbol(ctx.symbol()[0]),
                self.visitTerm(ctx.term()[0], {})
            )

        if ctx.cmd_defineConst():
            identifier = self.visitSymbol(ctx.symbol()[0])
            sort = self.visitSort(ctx.sort()[0])
            term = self.visitTerm(ctx.term()[0], {})
            self.add_to_globals(identifier, [], sort)
            return DefineConst(identifier, sort, term)

        if ctx.cmd_defineFun() or ctx.cmd_defineFunRec():
            fun_def = ctx.function_def()
            identifier = self.visitSymbol(fun_def.symbol())
            params, local_vars = self.visitSorted_vars(fun_def.sorted_var())
            sort = self.visitSort(fun_def.sort())
            sorted_vars = [
                self.visitSorted_var(var) for var in fun_def.sorted_var()
            ]
            if ctx.cmd_defineFunRec():
                # The body may call the function itself.
                self.add_to_globals(
                    identifier, [s for _, s in params], sort
                )
                term = self.visitTerm(fun_def.term(), local_vars)
                return DefineFunRec(identifier, sorted_vars, sort, term)
            term = self.visitTerm(fun_def.term(), local_vars)
            self.add_to_globals(identifier, [s for _, s in params], sort)
            return DefineFun(identifier, " ".join(sorted_vars), sort, term)

        if ctx.cmd_defineFunsRec():
            decls = []
            scopes = []
            for decl in ctx.function_dec():
                decls.append(self.visitFunction_dec(decl))
                params, local_vars = self.visitSorted_vars(decl.sorted_var())
                self.add_to_globals(
                    self.visitSymbol(decl.symbol()),
                    [s for _, s in params],
                    self.visitSort(decl.sort()),
                )
                scopes.append(local_vars)
            terms = []
            for term, local_vars in zip(ctx.term(), scopes):
                terms.append(self.visitTerm(term, local_vars))
            return DefineFunsRec(decls, terms)

        if ctx.cmd_checkSat():
            terms = []
            for t in ctx.term():
                terms.append(self.visitTerm(t, {}))
            if len(terms) > 0:
                return CheckSat(terms)
            return CheckSat()

        if ctx.cmd_checkSatAssuming():
            terms = []
            for t in ctx.term():
                terms.append(self.visitTerm(t, {}))
            return CheckSatAssuming(terms)

        if ctx.cmd_getValue():
            terms = []
            for t in ctx.term():
                terms.append(self.visitTerm(t, {}))
            return GetValue(terms)

        if ctx.cmd_push():
            terms = []
            for t in ctx.term():
                terms.append(self.visitTerm(t, {}))
            if len(terms) > 0:
                return Push(terms)
            return Push()

        if ctx.cmd_pop():
            terms = []
            for t in ctx.term():
                terms.append(self.visitTerm(t, {}))
            if len(terms) > 0:
                return Pop(terms)
            return Pop()

    def visitFunction_dec(self, ctx: SMTLIBv2Parser.Function_decContext):
        sorted_vars = []
        for var in ctx.sorted_var():
            sorted_vars.append(self.visitSorted_var(var))

        return FunDecl(
            self.visitSymbol(
                ctx.symbol()), sorted_vars, self.visitSort(ctx.sort())
        )

    def visitSorted_var(self, ctx: SMTLIBv2Parser.Sorted_varContext):
        return (
            "("
            + self.visitSymbol(ctx.symbol())
            + " "
            + self.visitSort(ctx.sort())
            + ")"
        )

    def getString(self, ctx):
        start, stop = ctx.start.start, ctx.stop.stop
        return ctx.start.getInputStream().getText(start, stop)

    def visitCommand(self, ctx: SMTLIBv2Parser.CommandContext):
        if not self.strict:
            try:
                cmd = self.handleCommand(ctx)
                if not cmd:
                    return SMTLIBCommand(self.getString(ctx))
                else:
                    return cmd
            except Exception:
                return SMTLIBCommand(self.getString(ctx))
        else:
            cmd = self.handleCommand(ctx)
            if not cmd:

                return SMTLIBCommand(self.getString(ctx))
            else:
                return cmd

    def visitAttribute(self, ctx: SMTLIBv2Parser.AttributeContext):
        """
        :returns: (keyword, value), value is the text of the attribute value
                  as in the input (getText() would drop the whitespace in
                  e.g. :pattern ((f x))) or None if there is no value
        """
        value = ctx.attribute_value()
        return (
            ctx.keyword().getText(),
            self.getString(value) if value else None,
        )

    def handle_quantifier(
            self,
            ctx: SMTLIBv2Parser.TermContext,
            quant,
            local_vars):

        subterms = []
        qvars = []
        qtypes = []
        for i in range(len(ctx.sorted_var())):
            qvar = self.visitSymbol(ctx.sorted_var()[i].symbol())
            qtype = self.visitSort(ctx.sorted_var()[i].sort())
            local_vars[qvar] = qtype
            qvars.append(qvar)
            qtypes.append(qtype)

        for t in ctx.term():
            subterms.append(self.visitTerm(t, local_vars))
        return Quantifier(quant, (qvars, qtypes), subterms)

    def visitSpec_constant(self, ctx: SMTLIBv2Parser.Spec_constantContext):
        """
        spec_constant
        : numeral
        | decimal
        | hexadecimal
        | binary
        | string
        | b_value
        | reg_const
        ;
        """
        if ctx.numeral():
            return ctx.getText().encode("utf-8").decode("utf-8"), INTEGER_TYPE
        if ctx.decimal():
            return ctx.getText().encode("utf-8").decode("utf-8"), REAL_TYPE
        if ctx.hexadecimal():
            # #xF0: a bit-vector of 4 bits per hexadecimal digit
            text = ctx.getText()
            return text, BITVECTOR_TYPE(4 * (len(text) - 2))
        if ctx.binary():
            # #b101: a bit-vector of 1 bit per binary digit
            text = ctx.getText()
            return text, BITVECTOR_TYPE(len(text) - 2)
        if ctx.string():
            return ctx.getText().encode("utf-8").decode("utf-8"), STRING_TYPE
        if ctx.b_value():
            return ctx.getText().encode("utf-8").decode("utf-8"), BOOLEAN_TYPE
        if ctx.reg_const():
            return ctx.getText().encode("utf-8").decode("utf-8"), REGEXP_TYPE

    def visitTerm(self, ctx: SMTLIBv2Parser.TermContext, local_vars):
        """
        term
        : spec_constant
        | qual_identifier
        | ParOpen qual_identifier term+ ParClose
        | ParOpen GRW_Underscore symbol numeral ParClose
        | ParOpen ParOpen GRW_Underscore qual_identifier term+ ParClose
          ParClose
        | ParOpen GRW_Let ParOpen var_binding+ ParClose term ParClose
        | ParOpen GRW_Forall ParOpen sorted_var+ ParClose term ParClose
        | ParOpen GRW_Exists ParOpen sorted_var+ ParClose term ParClose
        | ParOpen GRW_Match term ParOpen match_case+ ParClose ParClose
        | ParOpen GRW_Exclamation term attribute+ ParClose
        ;
        """

        if (
            ctx.ParOpen()
            and ctx.GRW_Exclamation()
            and ctx.term()
            and len(ctx.attribute()) >= 1
            and ctx.ParClose()
        ):
            term = self.visitTerm(ctx.term()[0], local_vars)
            attributes = [self.visitAttribute(a) for a in ctx.attribute()]
            return LabeledTerm(attributes, [term])

        if (
            len(ctx.ParOpen()) == 2
            and ctx.GRW_Match()
            and ctx.term()
            and len(ctx.match_case()) >= 1
        ):
            raise AstException(
                "ParOpen GRW_Match term ParOpen match_case+ ParClose ParClose"
            )

        if len(ctx.ParOpen()) == 1 and ctx.GRW_Underscore() and ctx.numeral():
            bv_value = ctx.symbol().getText()[len("bv"):]
            bitwidth = ctx.numeral().getText()
            return Const(
                name="(_ bv" + bv_value + " " + bitwidth + ")",
                type=BITVECTOR_TYPE(int(bitwidth)),
            )

        if (
            len(ctx.ParOpen()) == 2
            and ctx.GRW_Exists()
            and len(ctx.sorted_var()) >= 1
            and len(ctx.ParClose()) == 2
            and ctx.term()
        ):

            return self.handle_quantifier(ctx, "exists", local_vars)

        if (
            len(ctx.ParOpen()) == 2
            and ctx.GRW_Forall()
            and len(ctx.sorted_var()) >= 1
            and len(ctx.ParClose()) == 2
            and ctx.term()
        ):

            return self.handle_quantifier(ctx, "forall", local_vars)

        if (
            len(ctx.ParOpen()) == 2
            and ctx.GRW_Let()
            and ctx.var_binding()
            and len(ctx.ParClose()) == 2
            and ctx.term()
        ):

            terms = []
            var_list = []
            for b in ctx.var_binding():
                local_vars[self.visitSymbol(b.symbol())] = "Unknown"
                var_list.append(self.visitSymbol(b.symbol()))
                terms.append(self.visitTerm(b.term(), local_vars))
            subterms = []
            for sub in ctx.term():
                subterms.append(self.visitTerm(sub, local_vars=local_vars))
            return LetBinding(var_list, terms, subterms=subterms)

        if (
            ctx.ParOpen()
            and ctx.qual_identifier()
            and len(ctx.term()) >= 1
            and ctx.ParClose()
        ):

            op = self.visitQual_identifier(ctx.qual_identifier(), local_vars)
            subterms = []
            for term in ctx.term():
                subterms.append(self.visitTerm(term, local_vars))
            return Expr(op=op, subterms=subterms)

        if ctx.spec_constant():
            name, type = self.visitSpec_constant(ctx.spec_constant())
            return Const(name=name, type=type)

        if ctx.qual_identifier():
            return self.visitQual_identifier(ctx.qual_identifier(), local_vars)

        raise AstException("No match for term : ... |... |... ")

    def visitQual_identifier(
        self, ctx: SMTLIBv2Parser.Qual_identifierContext, local_vars
    ):
        """
        qual_identifier
        : identifier
        | ParOpen GRW_As identifier sort ParClose
        ;
        """

        if (
            ctx.ParOpen()
            and ctx.GRW_As()
            and ctx.identifier()
            and ctx.sort()
            and ctx.ParClose()
        ):
            # Qualified identifier, e.g. (as const (Array Int Int)) or
            # (as nil (List Int))
            identifier = self.identifier_text(ctx.identifier())
            sort = self.visitSort(ctx.sort())
            name = "(as " + identifier + " " + sort + ")"
            if identifier in self.constants:
                return Const(name=name, type=sort2type(sort))
            return name

        if ctx.identifier():
            return self.visitIdentifier(ctx.identifier(), local_vars)

        raise AstException("No match for qual_identifier: ... |... |... ")

    def visitSimpleSymbol(self, ctx: SMTLIBv2Parser.SimpleSymbolContext):
        return ctx.getText()

    def visitQuotedSymbol(self, ctx: SMTLIBv2Parser.QuotedSymbolContext):
        return ctx.getText()

    def visitSymbol(self, ctx: SMTLIBv2Parser.SymbolContext):
        """
        symbol
        : simpleSymbol
        | quotedSymbol
        ;
        """

        if ctx.simpleSymbol():
            return self.visitSimpleSymbol(ctx.simpleSymbol())

        if ctx.quotedSymbol():
            return self.visitQuotedSymbol(ctx.quotedSymbol())

    def visitIdentifier(
            self,
            ctx: SMTLIBv2Parser.IdentifierContext,
            local_vars):
        """
        identifier
        : symbol
        | ParOpen GRW_Underscore symbol index+ ParClose
        ;
        """

        if (
            ctx.ParOpen()
            and ctx.GRW_Underscore()
            and ctx.symbol()
            and len(ctx.index()) >= 1
            and ctx.ParClose()
        ):
            symbol = self.visitSymbol(ctx.symbol())
            indices = [ind.getText() for ind in ctx.index()]
            name = self.identifier_text(ctx)
            if name in local_vars:
                return Var(name=name, type=local_vars[name],
                           is_indexed_id=True)
            elif name in self.global_vars:
                return Var(name=name, type=self.global_vars[name],
                           is_indexed_id=True)
            elif symbol in FP_INDEXED_CONSTANTS and len(indices) == 2:
                # (_ +zero eb sb), (_ NaN eb sb), ...
                return Const(name=name, type=FP_TYPE(int(indices[0]),
                                                     int(indices[1])))
            else:
                return name

        if ctx.symbol():
            name = self.visitSymbol(ctx.symbol())
            if name in local_vars:
                return Var(name=name, type=local_vars[name])
            elif name in self.global_vars:
                return Var(name=name, type=self.global_vars[name])
            elif name in self.constants:
                return Const(name=name, type=sort2type(self.constants[name]))
            elif name in ROUNDING_MODES:
                return Const(name=name, type=ROUNDINGMODE_TYPE)
            else:
                return name
        raise AstException("No match for identifier: ... |... |... ")

    def identifier_text(self, ctx: SMTLIBv2Parser.IdentifierContext):
        """
        :returns: the identifier as a string, e.g. "x" or "(_ extract 7 4)"
        """
        symbol = self.visitSymbol(ctx.symbol())
        if ctx.GRW_Underscore():
            indices = [ind.getText() for ind in ctx.index()]
            return "(_ " + symbol + " " + " ".join(indices) + ")"
        return symbol

    def visitTerminal(self, ctx):
        return ctx.getText()

    def visitSort(self, ctx: SMTLIBv2Parser.SortContext):
        if len(ctx.sort()) >= 1:
            s = "(" + self.identifier_text(ctx.identifier())
            for sort in ctx.sort():
                s += " " + self.visitSort(sort)
            return s + ")"
        name = self.identifier_text(ctx.identifier())
        # Sort aliases from define-sort (without parameters)
        return self.sorts.get(name, name)
