from src.parsing.typechecker import*

def typecheck_recur(expr, ctxt=Context({},{})):
    av_expr = []
    expr_type = []
    if isinstance(expr, Term):
        if expr.subterms:
            for s in expr.subterms:
                new_av, new_type = typecheck_recur(s,ctxt)
                for i in range(len(new_av)):
                    av_expr.append(new_av[i])
                    expr_type.append(new_type[i])
            new_type = typecheck_expr(expr,ctxt)
            expr_type.append(new_type)
            av_expr.append(expr)
        else:
            av_expr.append(expr)
            expr_type.append(typecheck_expr(expr,ctxt))
    else:
        if expr.term:
            new_av, new_type = typecheck_recur(expr.term, ctxt)
            for i in range(len(new_av)):
                        av_expr.append(new_av[i])
                        expr_type.append(new_type[i])
    return av_expr, expr_type
