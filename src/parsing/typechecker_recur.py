from src.parsing.typechecker import*

# Dominik: maybe a different name, other than "typecheck_recur" would be appropriate 
# now since no typechecking is happening here any longer.  
def typecheck_recur(expr):
    av_expr = []
    expr_type = []
    if isinstance(expr, Term):
        if expr.subterms:
            for s in expr.subterms:
                new_av, new_type = typecheck_recur(s)
                av_expr += new_av
                expr_type += new_type
            new_type = expr.type #typecheck_expr(expr,ctxt)
            expr_type.append(new_type)
            av_expr.append(expr)
        else:
            av_expr.append(expr)
            # expr_type.append(typecheck_expr(expr,ctxt))
            expr_type.append(expr.type)
    else:
        if expr.term:
            new_av, new_type = typecheck_recur(expr.term)
            av_expr += new_av
            expr_type += new_type
    return av_expr, expr_type
