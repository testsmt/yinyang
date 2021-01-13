from antlr4 import *

from .ast import *
from .SMTLIBv2Parser import SMTLIBv2Parser
from .SMTLIBv2Visitor import *
from .util import *
from .types import *

class ASTVisitor(SMTLIBv2Visitor):
    def __init__(self, strict=True):
        self.strict = strict
        self.globals = {}
        self.sorts = {}

    def visitStart(self, ctx:SMTLIBv2Parser.StartContext):
        return self.visitScript(ctx.script())

    def visitScript(self, ctx:SMTLIBv2Parser.ScriptContext):
        cmds=[]
        for c in ctx.command():
            cmds.append(self.visitCommand(c))
        return Script(cmds,self.globals)

    def add_to_globals(self, identifier, input_sorts, output_sort):
        if len(input_sorts) == 0:
            if output_sort in self.sorts:
                output_sort = self.sorts[output_sort]
            self.globals[identifier] = sort2type(output_sort)
        else:
            self.globals[identifier] = sort2type(input_sorts +" "+ output_sort)

    def handleCommand(self, ctx:SMTLIBv2Parser.CommandContext):
        if ctx.cmd_assert():
            return Assert(self.visitTerm(ctx.term()[0]))
        if ctx.cmd_assertSoft():
            attr = []
            for a in ctx.attribute():
                a = self.visitAttribute(a)
                attr.append(a)
            return AssertSoft(self.visitTerm(ctx.term()[0]),attr)
        if ctx.cmd_simplify():
            attr = []
            for a in ctx.attribute():
                a = self.visitAttribute(a)
                attr.append(a)
            return Simplify(self.visitTerm(ctx.term()[0]), attr)
        if ctx.cmd_minimize():
            return Minimize(self.visitTerm(ctx.term()[0]))
        if ctx.cmd_maximize():
            return Maximize(self.visitTerm(ctx.term()[0]))
        if ctx.cmd_display():
            return Display(self.visitTerm(ctx.term()[0]))
        if ctx.cmd_eval():
            return Eval(self.visitTerm(ctx.term()[0]))
        if ctx.cmd_declareConst():
            self.add_to_globals(self.visitSymbol(ctx.symbol()[0]),[], self.visitSort(ctx.sort()[0]))
            decl = DeclareConst(self.visitSymbol(ctx.symbol()[0]), self.visitSort(ctx.sort()[0]))
            return decl
        if ctx.cmd_declareFun():
            input_sorts = []
            for sort in ctx.sort()[:-1]:
                input_sorts.append(self.visitSort(sort))
            output_sort = self.visitSort(ctx.sort()[-1])
            input_sorts = " ".join(input_sorts)
            identifier = self.visitSymbol(ctx.symbol()[0])
            self.add_to_globals(identifier, input_sorts, output_sort)
            return DeclareFun(identifier, input_sorts, output_sort)

        if ctx.cmd_define():
            return Define(self.visitSymbol(ctx.symbol()[0]), self.visitTerm(ctx.term()[0]))

        if ctx.cmd_defineConst():
            return DefineConst(self.visitSymbol(ctx.symbol()[0]),
                             self.visitSort(ctx.sort()[0]),
                             self.visitTerm(ctx.term()[0]))

        if ctx.cmd_defineFun():
            sorted_vars =  []
            for var in ctx.function_def().sorted_var():
               sorted_vars.append(self.visitSorted_var(var))
            identifier = self.visitSymbol(ctx.function_def().symbol())
            sorted_vars = " ".join(sorted_vars)
            self.add_to_globals(identifier,sorted_vars, self.visitSort(ctx.function_def().sort()))
            return DefineFun(identifier,
                             sorted_vars,
                             self.visitSort(ctx.function_def().sort()),
                             self.visitTerm(ctx.function_def().term()))

        if ctx.cmd_defineFunRec():
            sorted_vars = []
            for var in ctx.function_def().sorted_var():
               sorted_vars.append(self.visitSorted_var(var))
            return DefineFunRec(self.visitSymbol(ctx.function_def().symbol()),
                             sorted_vars,
                             self.visitSort(ctx.function_def().sort()),
                             self.visitTerm(ctx.function_def().term()))

        if ctx.cmd_defineFunsRec():
            decls = []
            for decl in ctx.function_dec():
                decls.append(self.visitFunction_dec(decl))
            terms = []
            for term in ctx.term():
                terms.append(self.visitTerm(term))
            return DefineFunsRec(decls,terms)

        if ctx.cmd_checkSat():
            terms = []
            for t in ctx.term():
                terms.append(self.visitTerm(t))
            if len(terms) > 0:
                return CheckSat(terms)
            return CheckSat()

        if ctx.cmd_checkSatAssuming():
            terms = []
            for t in ctx.term():
                terms.append(self.visitTerm(t))
            return CheckSatAssuming(terms)

        if ctx.cmd_getValue():
            terms = []
            for t in ctx.term():
                terms.append(self.visitTerm(t))
            return GetValue(terms)

        # Dominik: We do not need an explicit represention of the (define-sort
        # statements in the AST but need to add the defined sorts to the context.
        if ctx.cmd_defineSort():
            symbol = self.visitSymbol(ctx.symbol()[0])
            sort = self.visitSort(ctx.sort()[0])
            self.sort_ctxt[symbol] = sort

    def visitFunction_dec(self, ctx:SMTLIBv2Parser.Function_decContext):
        sorted_vars = []
        for var in ctx.sorted_var():
            sorted_vars.append(self.visitSorted_var(var))
        return FunDecl(self.visitSymbol(ctx.symbol()),
                       sorted_vars,
                       self.visitSort(ctx.sort()))

    def visitSorted_var(self, ctx:SMTLIBv2Parser.Sorted_varContext):
       return "("+ self.visitSymbol(ctx.symbol()) + " " +self.visitSort(ctx.sort()) +")"

    def getString(self,ctx):
        start, stop = ctx.start.start, ctx.stop.stop
        return ctx.start.getInputStream().getText(start, stop)

    def visitCommand(self, ctx:SMTLIBv2Parser.CommandContext):
        if not self.strict:
            try:
                cmd = self.handleCommand(ctx)
                if not cmd:
                    cmd_str = str(ctx.start.getInputStream())
                    return SMTLIBCommand(self.getString(ctx))
                else:
                    return cmd
            except:
                cmd_str = str(ctx.start.getInputStream())
                return SMTLIBCommand(self.getString(ctx))
        else:
            cmd = self.handleCommand(ctx)
            if not cmd:

                return SMTLIBCommand(self.getString(ctx))
            else:
                return cmd

    def visitAttribute(self, ctx:SMTLIBv2Parser.AttributeContext):
        return (ctx.keyword().getText(),ctx.attribute_value().getText())


    def handle_quantifier(self,ctx:SMTLIBv2Parser.TermContext, quant, local_vars={}):
        subterms = []
        qvars = []
        qtypes = []
        for i in range(len(ctx.sorted_var())):
            qvar =  self.visitSymbol(ctx.sorted_var()[i].symbol())
            qtype = self.visitSort(ctx.sorted_var()[i].sort())
            local_vars[qvar] = qtype
            qvars.append(qvar)
            qtypes.append(qtype)

        for t in ctx.term():
            subterms.append(self.visitTerm(t, local_vars))
        return Quantifier(quant, (qvars, qtypes), subterms)
    """
    spec_constant
    : numeral
    | decimal
    | hexadecimal
    | binary
    | string
    | b_value
    | ParOpen GRW_Underscore ' bv' numeral numeral ParClose
    ;
    """
    def visitSpec_constant(self, ctx:SMTLIBv2Parser.Spec_constantContext):
        if ctx.ParOpen():
            X,n = ctx.numeral()[0].getText(), ctx.numeral()[1].getText()
            return "(_ bv"+X+" "+n+")", BITVECTOR_TYPE(int(n))
        if ctx.numeral():
            return ctx.getText(),INTEGER_TYPE
        if ctx.decimal():
            return ctx.getText(),REAL_TYPE
        if ctx.hexadecimal():
            return ctx.getText(),INTEGER_TYPE
        if ctx.binary():
             return ctx.getText(),INTEGER_TYPE
        if ctx.string():
            return ctx.getText(),STRING_TYPE
        if ctx.b_value():
            return ctx.getText(),BOOLEAN_TYPE


    """
        term
            : spec_constant
            | qual_identifier
            | ParOpen qual_identifier term+ ParClose
            | ParOpen GRW_Let ParOpen var_binding+ ParClose term ParClose
            | ParOpen GRW_Forall ParOpen sorted_var+ ParClose term ParClose
            | ParOpen GRW_Exists ParOpen sorted_var+ ParClose term ParClose
            | ParOpen GRW_Match term ParOpen match_case+ ParClose ParClose
            | ParOpen GRW_Exclamation term attribute+ ParClose
            ;
    """
    def visitTerm(self, ctx:SMTLIBv2Parser.TermContext, local_vars={}):
        if ctx.ParOpen() and ctx.GRW_Exclamation() and ctx.term()\
           and len(ctx.attribute()) >= 1 and ctx.ParClose():
            term,label = self.visitTerm(ctx.term()[0]),self.visitAttribute(ctx.attribute()[0])
            return LabeledTerm(label, [term])

        if len(ctx.ParOpen()) == 2 and ctx.GRW_Match() and ctx.term() and len(ctx.match_case()) >= 1 and\
            len(ctx.ParClose()) == 2:
            raise ASTException("ParOpen GRW_Match term ParOpen match_case+ ParClose ParClose")

        if len(ctx.ParOpen()) == 2 and ctx.GRW_Exists() and len(ctx.sorted_var()) >= 1 and\
            len(ctx.ParClose()) == 2 and ctx.term():
            return self.handle_quantifier(ctx,"exists",local_vars)

        if len(ctx.ParOpen()) == 2 and ctx.GRW_Forall() and len(ctx.sorted_var()) >= 1 and\
           len(ctx.ParClose()) == 2 and ctx.term():
           return self.handle_quantifier(ctx,"forall", local_vars)

        if len(ctx.ParOpen()) == 2 and ctx.GRW_Let() and ctx.var_binding() and\
            len(ctx.ParClose()) == 2 and ctx.term():
            terms = []
            var_list = []
            for b in ctx.var_binding():
               local_vars[self.visitSymbol(b.symbol())] = UNKNOWN
               var_list.append(self.visitSymbol(b.symbol()))
               terms.append(self.visitTerm(b.term(),local_vars))
            subterms = []
            for sub in ctx.term():
                subterms.append(self.visitTerm(sub, local_vars=local_vars))
            return LetBinding(var_list, terms, subterms=subterms)

        if ctx.ParOpen() and ctx.qual_identifier() and len(ctx.term()) >= 1 and ctx.ParClose():
            op = self.visitQual_identifier(ctx.qual_identifier())
            subterms = []
            for term in ctx.term():
                subterms.append(self.visitTerm(term, local_vars))
            return Expr(op=op,subterms=subterms)

        if ctx.spec_constant():
            name,type=self.visitSpec_constant(ctx.spec_constant())
            return Const(name=name,type=type)

        if ctx.qual_identifier():
            return self.visitQual_identifier(ctx.qual_identifier(),local_vars)

        raise ASTException("No match for term : ... |... |... ")

    """
    qual_identifier
    : identifier
    | ParOpen GRW_As identifier sort ParClose [OK]
    ;
    """
    def visitQual_identifier(self,ctx:SMTLIBv2Parser.Qual_identifierContext, local_vars={}):
        if ctx.ParOpen() and ctx.GRW_As() and ctx.identifier() and ctx.sort() and\
            ctx.ParClose():
            raise ASTException("ParOpen GRW_As identifier sort ParClose")

        if ctx.identifier():
            return self.visitIdentifier(ctx.identifier(),local_vars)

        raise ASTException("No match for qual_identifier: ... |... |... ")


    def visitSimpleSymbol(self, ctx:SMTLIBv2Parser.SimpleSymbolContext):
        return ctx.getText()


    def visitQuotedSymbol(self, ctx:SMTLIBv2Parser.QuotedSymbolContext):
        return ctx.getText()

    """
    symbol
    : simpleSymbol
    | quotedSymbol
    ;
    """
    def visitSymbol(self, ctx:SMTLIBv2Parser.SymbolContext):
        if ctx.simpleSymbol():
            return self.visitSimpleSymbol(ctx.simpleSymbol())

        if ctx.quotedSymbol():
            return self.visitQuotedSymbol(ctx.quotedSymbol())

    """
    identifier
    : symbol
    | ParOpen GRW_Underscore symbol index+ ParClose
    ;
    """
    def visitIdentifier(self,ctx:SMTLIBv2Parser.IdentifierContext, local_vars=[]):
        if ctx.ParOpen() and ctx.GRW_Underscore() and ctx.symbol() and len(ctx.index()) >= 1 and\
           ctx.ParClose():
            symbol = self.visitSymbol(ctx.symbol())
            index = ctx.index()[0].getText()
            for ind in ctx.index()[1:]:
                index+= " "+ ind.getText()
            name = "(_ "+symbol +" "+ index+")"
            if name in local_vars:
                return Var(name=name, type=local_vars[name], is_indexed_id=True)
            elif name in self.globals:
                return Var(name=name, type=self.globals[name], is_indexed_id=True)
            else:
                return name

        if ctx.symbol():
            name = self.visitSymbol(ctx.symbol())
            if name in local_vars:
                return Var(name=name, type=local_vars[name])
            elif name in self.globals:
                return Var(name=name, type=self.globals[name])
            else:
                return self.visitSymbol(ctx.symbol())
        raise ASTException("No match for identifier: ... |... |... ")

    def visitTerminal(self,ctx):
        return ctx.getText()

    def visitSort(self, ctx:SMTLIBv2Parser.SortContext):
        if len(ctx.sort()) >= 1:
            s = "("+ self.visitIdentifier(ctx.identifier())
            for sort in ctx.sort():
                s += " "+ self.visitSort(sort)
            return s+")"
        return self.visitIdentifier(ctx.identifier())
