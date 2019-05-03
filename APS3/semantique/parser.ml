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
  | NTH
  | VEC
  | LEN
  | ALLOC
  | RETURN

open Parsing;;
let _ = parse_error;;
# 5 "parser.mly"
open Ast
# 50 "parser.ml"
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
  294 (* NTH *);
  295 (* VEC *);
  296 (* LEN *);
  297 (* ALLOC *);
  298 (* RETURN *);
    0|]

let yytransl_block = [|
  257 (* NUM *);
  258 (* IDENT *);
    0|]

let yylhs = "\255\255\
\001\000\002\000\004\000\004\000\004\000\004\000\004\000\004\000\
\004\000\004\000\004\000\004\000\004\000\004\000\004\000\004\000\
\004\000\004\000\004\000\004\000\004\000\006\000\006\000\007\000\
\007\000\007\000\007\000\007\000\008\000\008\000\009\000\009\000\
\009\000\009\000\009\000\009\000\012\000\005\000\005\000\013\000\
\013\000\014\000\014\000\014\000\014\000\014\000\015\000\010\000\
\010\000\010\000\010\000\003\000\011\000\000\000"

let yylen = "\002\000\
\001\000\001\000\001\000\001\000\005\000\005\000\005\000\005\000\
\005\000\005\000\006\000\004\000\004\000\004\000\005\000\005\000\
\001\000\001\000\004\000\004\000\005\000\001\000\002\000\001\000\
\001\000\005\000\001\000\004\000\001\000\003\000\004\000\009\000\
\010\000\003\000\006\000\007\000\003\000\001\000\003\000\001\000\
\005\000\002\000\004\000\003\000\003\000\003\000\002\000\001\000\
\003\000\003\000\001\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\054\000\001\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\051\000\000\000\000\000\000\000\003\000\004\000\
\017\000\018\000\000\000\000\000\042\000\000\000\000\000\000\000\
\040\000\000\000\000\000\000\000\000\000\000\000\047\000\000\000\
\052\000\000\000\000\000\025\000\024\000\027\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\034\000\000\000\000\000\000\000\046\000\000\000\
\000\000\044\000\000\000\045\000\049\000\050\000\000\000\000\000\
\000\000\031\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\043\000\023\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\014\000\000\000\000\000\019\000\020\000\013\000\037\000\012\000\
\039\000\000\000\000\000\000\000\053\000\028\000\030\000\000\000\
\000\000\000\000\005\000\006\000\007\000\008\000\010\000\009\000\
\015\000\016\000\000\000\021\000\035\000\000\000\041\000\026\000\
\000\000\000\000\011\000\036\000\000\000\000\000\032\000\000\000\
\033\000"

let yydgoto = "\002\000\
\004\000\000\000\005\000\075\000\065\000\076\000\080\000\081\000\
\016\000\017\000\073\000\066\000\035\000\018\000\019\000"

let yysindex = "\009\000\
\251\254\000\000\111\255\000\000\000\000\013\255\005\255\060\255\
\014\255\007\255\016\255\060\255\060\255\015\255\060\255\001\255\
\004\255\006\255\000\000\000\255\000\255\032\255\000\000\000\000\
\000\000\000\000\118\255\040\255\000\000\000\255\043\255\058\255\
\000\000\026\255\060\255\052\255\052\255\060\255\000\000\111\255\
\000\000\111\255\246\254\000\000\000\000\000\000\060\255\054\255\
\000\255\060\255\060\255\060\255\060\255\060\255\060\255\060\255\
\060\255\060\255\060\255\060\255\060\255\060\255\060\255\053\255\
\069\255\070\255\000\000\040\255\061\255\016\255\000\000\111\255\
\052\255\000\000\060\255\000\000\000\000\000\000\000\255\072\255\
\073\255\000\000\040\255\074\255\060\255\060\255\060\255\060\255\
\060\255\060\255\060\255\060\255\080\255\060\255\060\255\083\255\
\084\255\085\255\000\255\060\255\040\255\086\255\040\255\060\255\
\087\255\000\000\000\000\090\255\000\255\000\255\089\255\040\255\
\092\255\093\255\094\255\095\255\096\255\097\255\099\255\102\255\
\000\000\060\255\122\255\000\000\000\000\000\000\000\000\000\000\
\000\000\052\255\116\255\124\255\000\000\000\000\000\000\132\255\
\133\255\131\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\135\255\000\000\000\000\052\255\000\000\000\000\
\111\255\136\255\000\000\000\000\134\255\111\255\000\000\137\255\
\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\138\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\140\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\048\255\000\000\000\000\000\000\000\000\139\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000"

let yygindex = "\000\000\
\000\000\000\000\000\000\249\255\211\255\250\255\248\255\052\000\
\000\000\216\255\222\255\000\000\031\000\000\000\000\000"

let yytablesize = 161
let yytable = "\077\000\
\029\000\078\000\074\000\043\000\036\000\037\000\021\000\039\000\
\031\000\001\000\003\000\047\000\048\000\043\000\020\000\030\000\
\038\000\033\000\040\000\063\000\041\000\067\000\102\000\042\000\
\044\000\045\000\046\000\071\000\079\000\034\000\022\000\105\000\
\032\000\049\000\044\000\045\000\046\000\111\000\106\000\082\000\
\084\000\064\000\085\000\086\000\087\000\088\000\089\000\090\000\
\091\000\092\000\093\000\094\000\095\000\096\000\097\000\129\000\
\098\000\131\000\068\000\069\000\023\000\024\000\022\000\070\000\
\022\000\022\000\138\000\072\000\107\000\083\000\108\000\025\000\
\026\000\027\000\099\000\028\000\103\000\113\000\114\000\115\000\
\116\000\117\000\118\000\119\000\120\000\100\000\122\000\123\000\
\101\000\112\000\127\000\109\000\128\000\110\000\121\000\149\000\
\132\000\124\000\125\000\126\000\104\000\136\000\130\000\133\000\
\134\000\137\000\139\000\140\000\141\000\142\000\143\000\144\000\
\157\000\145\000\147\000\156\000\146\000\160\000\023\000\024\000\
\050\000\051\000\052\000\053\000\054\000\055\000\056\000\057\000\
\058\000\025\000\026\000\027\000\150\000\028\000\006\000\007\000\
\148\000\008\000\151\000\009\000\010\000\011\000\012\000\013\000\
\014\000\059\000\152\000\154\000\153\000\155\000\159\000\158\000\
\015\000\161\000\048\000\060\000\038\000\061\000\062\000\029\000\
\135\000"

let yycheck = "\040\000\
\008\000\042\000\037\000\014\001\012\000\013\000\002\001\015\000\
\002\001\001\000\016\001\020\000\021\000\014\001\002\001\002\001\
\002\001\002\001\018\001\027\000\017\001\030\000\068\000\018\001\
\035\001\036\001\037\001\035\000\039\001\014\001\026\001\072\000\
\026\001\002\001\035\001\036\001\037\001\083\000\073\000\047\000\
\049\000\002\001\050\000\051\000\052\000\053\000\054\000\055\000\
\056\000\057\000\058\000\059\000\060\000\061\000\062\000\101\000\
\063\000\103\000\016\001\002\001\001\001\002\001\015\001\038\001\
\017\001\018\001\112\000\016\001\075\000\016\001\079\000\012\001\
\013\001\014\001\022\001\016\001\016\001\085\000\086\000\087\000\
\088\000\089\000\090\000\091\000\092\000\017\001\094\000\095\000\
\019\001\016\001\099\000\020\001\100\000\021\001\015\001\130\000\
\104\000\015\001\015\001\015\001\070\000\110\000\017\001\017\001\
\015\001\017\001\015\001\015\001\015\001\015\001\015\001\015\001\
\153\000\015\001\122\000\150\000\015\001\158\000\001\001\002\001\
\003\001\004\001\005\001\006\001\007\001\008\001\009\001\010\001\
\011\001\012\001\013\001\014\001\017\001\016\001\024\001\025\001\
\015\001\027\001\015\001\029\001\030\001\031\001\032\001\033\001\
\034\001\028\001\015\001\017\001\016\001\015\001\017\001\016\001\
\042\001\017\001\017\001\038\001\017\001\040\001\041\001\021\001\
\109\000"

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
  NTH\000\
  VEC\000\
  LEN\000\
  ALLOC\000\
  RETURN\000\
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
# 22 "parser.mly"
         (_1)
# 296 "parser.ml"
               : Ast.prog))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 26 "parser.mly"
                        ( _1 )
# 303 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 29 "parser.mly"
                             ( ASTNum(_1) )
# 310 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 30 "parser.mly"
                             ( ASTId(_1) )
# 317 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 31 "parser.mly"
                             ( ASTOPrim(Ast.Add, _3, _4) )
# 325 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 32 "parser.mly"
                             ( ASTOPrim(Ast.Sub, _3, _4) )
# 333 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 33 "parser.mly"
                             ( ASTOPrim(Ast.Mul, _3, _4) )
# 341 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 34 "parser.mly"
                             ( ASTOPrim(Ast.Div, _3, _4) )
# 349 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 35 "parser.mly"
                            ( ASTOPrim(Ast.Eq, _3, _4) )
# 357 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 36 "parser.mly"
                            ( ASTOPrim(Ast.Lt, _3, _4) )
# 365 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 37 "parser.mly"
                              (ASTIf(_3,_4,_5))
# 374 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 38 "parser.mly"
                      (ASTFuncExpr(_2,_4))
# 382 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'exprs) in
    Obj.repr(
# 39 "parser.mly"
                       (ASTExprs(_2,_3))
# 390 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 40 "parser.mly"
                         ( ASTNot(Ast.Not, _3) )
# 397 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 41 "parser.mly"
                           ( ASTBPrim(Ast.And , _3,_4) )
# 405 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 42 "parser.mly"
                           ( ASTBPrim(Ast.Or, _3,_4) )
# 413 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 43 "parser.mly"
        ( ASTBool(true) )
# 419 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 44 "parser.mly"
        ( ASTBool(false) )
# 425 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 45 "parser.mly"
                     (Len(_3))
# 432 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 46 "parser.mly"
                       (Alloc(_3))
# 439 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 47 "parser.mly"
                          (ASTNth(_3,_4))
# 447 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 51 "parser.mly"
       (Expr(_1))
# 454 "parser.ml"
               : 'exprs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'exprs) in
    Obj.repr(
# 52 "parser.mly"
            (Exprs(_1,_2))
# 462 "parser.ml"
               : 'exprs))
; (fun __caml_parser_env ->
    Obj.repr(
# 56 "parser.mly"
     (TPRIM(Ast.Int))
# 468 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    Obj.repr(
# 57 "parser.mly"
      (TPRIM(Ast.Bool))
# 474 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'types) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'letype) in
    Obj.repr(
# 58 "parser.mly"
                               (TypeFunc(_2,_4))
# 482 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    Obj.repr(
# 59 "parser.mly"
      (VOID)
# 488 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'letype) in
    Obj.repr(
# 60 "parser.mly"
                      (TypeVec(_3))
# 495 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'letype) in
    Obj.repr(
# 64 "parser.mly"
          (Type(_1))
# 502 "parser.ml"
               : 'types))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'letype) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'types) in
    Obj.repr(
# 65 "parser.mly"
                     (Types(_1,_3))
# 510 "parser.ml"
               : 'types))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'letype) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 70 "parser.mly"
                          (Const(_2,_3,_4))
# 519 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 6 : 'letype) in
    let _5 = (Parsing.peek_val __caml_parser_env 4 : 'args) in
    let _8 = (Parsing.peek_val __caml_parser_env 1 : 'cmds) in
    Obj.repr(
# 71 "parser.mly"
                                                  (Fun(_2,_3,_5,_8))
# 529 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 7 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 6 : 'letype) in
    let _6 = (Parsing.peek_val __caml_parser_env 4 : 'args) in
    let _9 = (Parsing.peek_val __caml_parser_env 1 : 'cmds) in
    Obj.repr(
# 72 "parser.mly"
                                                      (FunRec(_3,_4,_6,_9))
# 539 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'letype) in
    Obj.repr(
# 73 "parser.mly"
                   (Var(_2,_3))
# 547 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 74 "parser.mly"
                                  (ASTProc(_2,_4,_6))
# 556 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 75 "parser.mly"
                                      (ASTProcRec(_3,_5,_7))
# 565 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'letype) in
    Obj.repr(
# 80 "parser.mly"
                      (ASTArg(_1,_3))
# 573 "parser.ml"
               : 'arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arg) in
    Obj.repr(
# 84 "parser.mly"
     (Arg(_1))
# 580 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arg) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'args) in
    Obj.repr(
# 85 "parser.mly"
                (Args(_1,_3))
# 588 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 90 "parser.mly"
       (IdentLval(_1))
# 595 "parser.ml"
               : 'lval))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'lval) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 91 "parser.mly"
                        (Nth(_3,_4))
# 603 "parser.ml"
               : 'lval))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 96 "parser.mly"
           (Echo(_2))
# 610 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'block) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 97 "parser.mly"
                          (IfProc(_2,_3,_4))
# 619 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 98 "parser.mly"
                  (ASTWhile(_2,_3))
# 627 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exprs) in
    Obj.repr(
# 99 "parser.mly"
                  (ASTCall(_2,_3))
# 635 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'lval) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 100 "parser.mly"
               (SetLval(_2,_3))
# 643 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 104 "parser.mly"
             (Return(_2))
# 650 "parser.ml"
               : 'ret))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stat) in
    Obj.repr(
# 108 "parser.mly"
      (Stats(_1))
# 657 "parser.ml"
               : 'cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'dec) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cmds) in
    Obj.repr(
# 109 "parser.mly"
                      (Dec(_1,_3))
# 665 "parser.ml"
               : 'cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'stat) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cmds) in
    Obj.repr(
# 110 "parser.mly"
                      (Stat(_1,_3))
# 673 "parser.ml"
               : 'cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'ret) in
    Obj.repr(
# 111 "parser.mly"
     (Ret(_1))
# 680 "parser.ml"
               : 'cmds))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'cmds) in
    Obj.repr(
# 115 "parser.mly"
                (Cmds(_2))
# 687 "parser.ml"
               : 'prog))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'cmds) in
    Obj.repr(
# 119 "parser.mly"
                (CmdsBlock(_2))
# 694 "parser.ml"
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
