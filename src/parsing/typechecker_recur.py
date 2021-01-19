from src.parsing.typechecker import*

def typecheck_recur(expr, ctxt=Context({},{})):
    av_expr = []
    expr_type = []
    if isinstance(expr, Term):
        if expr.subterms:
            for s in expr.subterms:
                new_av, new_type = typecheck_recur(s,ctxt)
                av_expr += new_av
                expr_type += new_type
            new_type = typecheck_expr(expr,ctxt)
            expr_type.append(new_type)
            av_expr.append(expr)
        else:
            av_expr.append(expr)
            expr_type.append(typecheck_expr(expr,ctxt))
    else:
        if expr.term:
            new_av, new_type = typecheck_recur(expr.term, ctxt)
            av_expr += new_av
            expr_type += new_type
    return av_expr, expr_type
