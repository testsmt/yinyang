def debug(ctx,n):
    print("######### BEGIN DEBUG"+n+"################")
    print(ctx.getText())
    print("######### END DEBUG ################")

class ASTException(Exception):
    pass
