type token =
  | NUM of (int)
  | IDENT of (string)
  | PLUS
  | MINUS
  | TIMES
  | DIV
  | LT
  | EQ
  | AND
  | OR
  | NOT
  | TRUE
  | FALSE
  | LPAR
  | RPAR
  | LCRO
  | RCRO
  | SEPARATOR
  | VIRGU
  | ETOILE
  | FLECHE
  | DPOINTS
  | EOL
  | CONST
  | FUN
  | REC
  | ECHO
  | IF
  | VAR
  | PROC
  | SET
  | IF_PROC
  | WHILE
  | CALL
  | BOOL
  | INT
  | VOID

open Parsing;;
let _ = parse_error;;
# 5 "parser.mly"
open Ast
# 45 "parser.ml"
let yytransl_const = [|
  259 (* PLUS *);
  260 (* MINUS *);
  261 (* TIMES *);
  262 (* DIV *);
  263 (* LT *);
  264 (* EQ *);
  265 (* AND *);
  266 (* OR *);
  267 (* NOT *);
  268 (* TRUE *);
  269 (* FALSE *);
  270 (* LPAR *);
  271 (* RPAR *);
  272 (* LCRO *);
  273 (* RCRO *);
  274 (* SEPARATOR *);
  275 (* VIRGU *);
  276 (* ETOILE *);
  277 (* FLECHE *);
  278 (* DPOINTS *);
  279 (* EOL *);
  280 (* CONST *);
  281 (* FUN *);
  282 (* REC *);
  283 (* ECHO *);
  284 (* IF *);
  285 (* VAR *);
  286 (* PROC *);
  287 (* SET *);
  288 (* IF_PROC *);
  289 (* WHILE *);
  290 (* CALL *);
  291 (* BOOL *);
  292 (* INT *);
  293 (* VOID *);
    0|]

let yytransl_block = [|
  257 (* NUM *);
  258 (* IDENT *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\004\000\004\000\004\000\004\000\004\000\004\000\
\004\000\004\000\004\000\004\000\004\000\004\000\004\000\004\000\
\004\000\004\000\006\000\006\000\007\000\007\000\007\000\007\000\
\008\000\008\000\009\000\009\000\009\000\009\000\009\000\009\000\
\011\000\005\000\005\000\012\000\012\000\012\000\012\000\012\000\
\013\000\013\000\013\000\003\000\010\000\000\000"

let yylen = "\002\000\
\001\000\001\000\001\000\001\000\005\000\005\000\005\000\005\000\
\005\000\005\000\006\000\004\000\004\000\004\000\005\000\005\000\
\001\000\001\000\001\000\002\000\001\000\001\000\005\000\001\000\
\001\000\003\000\004\000\007\000\008\000\003\000\006\000\007\000\
\003\000\001\000\003\000\002\000\003\000\004\000\003\000\003\000\
\001\000\003\000\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\046\000\001\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\003\000\004\000\017\000\018\000\
\000\000\000\000\036\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\044\000\000\000\022\000\021\000\
\024\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\030\000\000\000\000\000\037\000\000\000\000\000\
\039\000\000\000\040\000\042\000\043\000\000\000\000\000\027\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\038\000\020\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\014\000\000\000\013\000\033\000\012\000\035\000\000\000\
\000\000\045\000\026\000\000\000\000\000\000\000\005\000\006\000\
\007\000\008\000\010\000\009\000\015\000\016\000\000\000\031\000\
\000\000\023\000\028\000\000\000\011\000\032\000\029\000"

let yydgoto = "\002\000\
\004\000\000\000\005\000\066\000\057\000\067\000\070\000\071\000\
\015\000\064\000\058\000\016\000\017\000"

let yysindex = "\007\000\
\002\255\000\000\058\255\000\000\000\000\012\255\005\255\050\255\
\019\255\010\255\022\255\050\255\050\255\023\255\008\255\029\255\
\032\255\248\254\248\254\051\255\000\000\000\000\000\000\000\000\
\109\255\052\255\000\000\248\254\039\255\054\255\050\255\042\255\
\042\255\050\255\058\255\058\255\000\000\248\254\000\000\000\000\
\000\000\050\255\043\255\248\254\050\255\050\255\050\255\050\255\
\050\255\050\255\050\255\050\255\050\255\050\255\050\255\038\255\
\044\255\046\255\000\000\052\255\059\255\000\000\058\255\042\255\
\000\000\050\255\000\000\000\000\000\000\061\255\057\255\000\000\
\052\255\068\255\050\255\050\255\050\255\050\255\050\255\050\255\
\050\255\050\255\078\255\050\255\079\255\248\254\050\255\052\255\
\081\255\052\255\083\255\000\000\000\000\248\254\248\254\084\255\
\052\255\080\255\087\255\088\255\089\255\090\255\091\255\092\255\
\093\255\000\000\050\255\000\000\000\000\000\000\000\000\042\255\
\110\255\000\000\000\000\111\255\050\255\112\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\113\255\000\000\
\042\255\000\000\000\000\050\255\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\114\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\115\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\254\254\000\000\000\000\000\000\075\255\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\000\000\248\255\216\255\212\255\247\255\036\000\
\000\000\224\255\000\000\000\000\223\255"

let yytablesize = 137
let yytable = "\027\000\
\065\000\068\000\069\000\032\000\033\000\038\000\019\000\001\000\
\042\000\043\000\085\000\029\000\019\000\018\000\019\000\019\000\
\055\000\003\000\059\000\089\000\028\000\093\000\062\000\031\000\
\034\000\035\000\039\000\040\000\041\000\091\000\020\000\092\000\
\096\000\072\000\074\000\030\000\075\000\076\000\077\000\078\000\
\079\000\080\000\081\000\082\000\083\000\084\000\036\000\111\000\
\037\000\113\000\021\000\022\000\044\000\056\000\060\000\061\000\
\118\000\063\000\073\000\086\000\087\000\023\000\024\000\025\000\
\088\000\026\000\098\000\099\000\100\000\101\000\102\000\103\000\
\104\000\105\000\090\000\107\000\109\000\095\000\110\000\128\000\
\094\000\006\000\007\000\097\000\008\000\116\000\009\000\010\000\
\011\000\012\000\013\000\014\000\106\000\108\000\119\000\025\000\
\134\000\112\000\127\000\114\000\117\000\120\000\121\000\122\000\
\123\000\124\000\125\000\126\000\131\000\021\000\022\000\045\000\
\046\000\047\000\048\000\049\000\050\000\051\000\052\000\053\000\
\023\000\024\000\025\000\135\000\026\000\130\000\129\000\133\000\
\132\000\115\000\041\000\034\000\000\000\000\000\000\000\000\000\
\054\000"

let yycheck = "\008\000\
\033\000\035\000\036\000\012\000\013\000\014\001\002\001\001\000\
\018\000\019\000\055\000\002\001\015\001\002\001\017\001\018\001\
\025\000\016\001\028\000\060\000\002\001\066\000\031\000\002\001\
\002\001\018\001\035\001\036\001\037\001\063\000\026\001\064\000\
\073\000\042\000\044\000\026\001\045\000\046\000\047\000\048\000\
\049\000\050\000\051\000\052\000\053\000\054\000\018\001\088\000\
\017\001\090\000\001\001\002\001\002\001\002\001\016\001\002\001\
\097\000\016\001\016\001\022\001\017\001\012\001\013\001\014\001\
\019\001\016\001\075\000\076\000\077\000\078\000\079\000\080\000\
\081\000\082\000\016\001\084\000\086\000\021\001\087\000\112\000\
\020\001\024\001\025\001\016\001\027\001\095\000\029\001\030\001\
\031\001\032\001\033\001\034\001\015\001\015\001\015\001\021\001\
\129\000\017\001\107\000\017\001\017\001\015\001\015\001\015\001\
\015\001\015\001\015\001\015\001\117\000\001\001\002\001\003\001\
\004\001\005\001\006\001\007\001\008\001\009\001\010\001\011\001\
\012\001\013\001\014\001\132\000\016\001\015\001\017\001\015\001\
\017\001\094\000\017\001\017\001\255\255\255\255\255\255\255\255\
\028\001"

let yynames_const = "\
  PLUS\000\
  MINUS\000\
  TIMES\000\
  DIV\000\
  LT\000\
  EQ\000\
  AND\000\
  OR\000\
  NOT\000\
  TRUE\000\
  FALSE\000\
  LPAR\000\
  RPAR\000\
  LCRO\000\
  RCRO\000\
  SEPARATOR\000\
  VIRGU\000\
  ETOILE\000\
  FLECHE\000\
  DPOINTS\000\
  EOL\000\
  CONST\000\
  FUN\000\
  REC\000\
  ECHO\000\
  IF\000\
  VAR\000\
  PROC\000\
  SET\000\
  IF_PROC\000\
  WHILE\000\
  CALL\000\
  BOOL\000\
  INT\000\
  VOID\000\
  "

let yynames_block = "\
  NUM\000\
  IDENT\000\
  "

let yyact = [|
  (fun _ -> failwith "parser")
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'prog) in
    Obj.repr(
# 20 "parser.mly"
         (_1)
# 261 "parser.ml"
               : Ast.prog))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 24 "parser.mly"
                        ( _1 )
# 268 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 27 "parser.mly"
                             ( ASTNum(_1) )
# 275 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 28 "parser.mly"
                             ( ASTId(_1) )
# 282 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 29 "parser.mly"
                             ( ASTOPrim(Ast.Add, _3, _4) )
# 290 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 30 "parser.mly"
                             ( ASTOPrim(Ast.Sub, _3, _4) )
# 298 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 31 "parser.mly"
                             ( ASTOPrim(Ast.Mul, _3, _4) )
# 306 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 32 "parser.mly"
                             ( ASTOPrim(Ast.Div, _3, _4) )
# 314 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 33 "parser.mly"
                            ( ASTOPrim(Ast.Eq, _3, _4) )
# 322 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 34 "parser.mly"
                            ( ASTOPrim(Ast.Lt, _3, _4) )
# 330 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 35 "parser.mly"
                              (ASTIf(_3,_4,_5))
# 339 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 36 "parser.mly"
                      (ASTFuncExpr(_2,_4))
# 347 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'exprs) in
    Obj.repr(
# 37 "parser.mly"
                       (ASTExprs(_2,_3))
# 355 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 40 "parser.mly"
                         ( ASTNot(Ast.Not, _3) )
# 362 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 41 "parser.mly"
                           ( ASTBPrim(Ast.And , _3,_4) )
# 370 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 42 "parser.mly"
                           ( ASTBPrim(Ast.Or, _3,_4) )
# 378 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 43 "parser.mly"
        ( ASTBool(true) )
# 384 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 44 "parser.mly"
        ( ASTBool(false) )
# 390 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 48 "parser.mly"
       (Expr(_1))
# 397 "parser.ml"
               : 'exprs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'exprs) in
    Obj.repr(
# 49 "parser.mly"
            (Exprs(_1,_2))
# 405 "parser.ml"
               : 'exprs))
; (fun __caml_parser_env ->
    Obj.repr(
# 53 "parser.mly"
     (TPRIM(Ast.Int))
# 411 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    Obj.repr(
# 54 "parser.mly"
      (TPRIM(Ast.Bool))
# 417 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'types) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'letype) in
    Obj.repr(
# 55 "parser.mly"
                               (TypeFunc(_2,_4))
# 425 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    Obj.repr(
# 56 "parser.mly"
      (VOID)
# 431 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'letype) in
    Obj.repr(
# 60 "parser.mly"
          (Type(_1))
# 438 "parser.ml"
               : 'types))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'letype) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'types) in
    Obj.repr(
# 61 "parser.mly"
                     (Types(_1,_3))
# 446 "parser.ml"
               : 'types))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'letype) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 66 "parser.mly"
                          (Const(_2,_3,_4))
# 455 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'letype) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 67 "parser.mly"
                                       (Fun(_2,_3,_5,_7))
# 465 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'letype) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 68 "parser.mly"
                                           (FunRec(_3,_4,_6,_8))
# 475 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'letype) in
    Obj.repr(
# 69 "parser.mly"
                   (Var(_2,_3))
# 483 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 70 "parser.mly"
                                  (ASTProc(_2,_4,_6))
# 492 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 71 "parser.mly"
                                      (ASTProcRec(_3,_5,_7))
# 501 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'letype) in
    Obj.repr(
# 76 "parser.mly"
                      (ASTArg(_1,_3))
# 509 "parser.ml"
               : 'arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arg) in
    Obj.repr(
# 80 "parser.mly"
     (Arg(_1))
# 516 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arg) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'args) in
    Obj.repr(
# 81 "parser.mly"
                (Args(_1,_3))
# 524 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 85 "parser.mly"
           (Echo(_2))
# 531 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 86 "parser.mly"
                (Set(_2,_3))
# 539 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'block) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 87 "parser.mly"
                          (IfProc(_2,_3,_4))
# 548 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 88 "parser.mly"
                  (ASTWhile(_2,_3))
# 556 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exprs) in
    Obj.repr(
# 89 "parser.mly"
                  (ASTCall(_2,_3))
# 564 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stat) in
    Obj.repr(
# 93 "parser.mly"
      (Stats(_1))
# 571 "parser.ml"
               : 'cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'dec) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cmds) in
    Obj.repr(
# 94 "parser.mly"
                      (Dec(_1,_3))
# 579 "parser.ml"
               : 'cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'stat) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cmds) in
    Obj.repr(
# 95 "parser.mly"
                      (Stat(_1,_3))
# 587 "parser.ml"
               : 'cmds))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'cmds) in
    Obj.repr(
# 99 "parser.mly"
                (Cmds(_2))
# 594 "parser.ml"
               : 'prog))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'cmds) in
    Obj.repr(
# 103 "parser.mly"
                (CmdsBlock(_2))
# 601 "parser.ml"
               : 'block))
(* Entry program *)
; (fun __caml_parser_env -> raise (Parsing.YYexit (Parsing.peek_val __caml_parser_env 0)))
|]
let yytables =
  { Parsing.actions=yyact;
    Parsing.transl_const=yytransl_const;
    Parsing.transl_block=yytransl_block;
    Parsing.lhs=yylhs;
    Parsing.len=yylen;
    Parsing.defred=yydefred;
    Parsing.dgoto=yydgoto;
    Parsing.sindex=yysindex;
    Parsing.rindex=yyrindex;
    Parsing.gindex=yygindex;
    Parsing.tablesize=yytablesize;
    Parsing.table=yytable;
    Parsing.check=yycheck;
    Parsing.error_function=parse_error;
    Parsing.names_const=yynames_const;
    Parsing.names_block=yynames_block }
let program (lexfun : Lexing.lexbuf -> token) (lexbuf : Lexing.lexbuf) =
   (Parsing.yyparse yytables 1 lexfun lexbuf : Ast.prog)
