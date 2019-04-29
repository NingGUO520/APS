mem(X,[X|_]).
mem(X,[_|Z]):-mem(X,Z).
astExprs(astFuncExpr([(x,int)],add(x,5)),[37])


