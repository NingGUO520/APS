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

open Parsing;;
let _ = parse_error;;
# 5 "parser.mly"
open Ast
# 49 "parser.ml"
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
\009\000\009\000\009\000\009\000\011\000\005\000\005\000\012\000\
\012\000\013\000\013\000\013\000\013\000\013\000\014\000\014\000\
\014\000\003\000\010\000\000\000"

let yylen = "\002\000\
\001\000\001\000\001\000\001\000\005\000\005\000\005\000\005\000\
\005\000\005\000\006\000\004\000\004\000\004\000\005\000\005\000\
\001\000\001\000\004\000\004\000\005\000\001\000\002\000\001\000\
\001\000\005\000\001\000\004\000\001\000\003\000\004\000\007\000\
\008\000\003\000\006\000\007\000\003\000\001\000\003\000\001\000\
\005\000\002\000\004\000\003\000\003\000\003\000\001\000\003\000\
\003\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\052\000\001\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\003\000\004\000\017\000\018\000\
\000\000\000\000\042\000\000\000\000\000\000\000\040\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\050\000\000\000\
\025\000\024\000\027\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\034\000\
\000\000\000\000\000\000\046\000\000\000\000\000\044\000\000\000\
\045\000\048\000\049\000\000\000\000\000\000\000\031\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\043\000\023\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\014\000\000\000\000\000\
\019\000\020\000\013\000\037\000\012\000\039\000\000\000\000\000\
\000\000\051\000\028\000\030\000\000\000\000\000\000\000\005\000\
\006\000\007\000\008\000\010\000\009\000\015\000\016\000\000\000\
\021\000\035\000\000\000\041\000\026\000\032\000\000\000\011\000\
\036\000\033\000"

let yydgoto = "\002\000\
\004\000\000\000\005\000\072\000\062\000\073\000\077\000\078\000\
\015\000\070\000\063\000\033\000\016\000\017\000"

let yysindex = "\006\000\
\254\254\000\000\091\255\000\000\000\000\013\255\001\255\086\255\
\014\255\004\255\255\254\086\255\086\255\016\255\005\255\006\255\
\009\255\055\255\055\255\053\255\000\000\000\000\000\000\000\000\
\126\255\056\255\000\000\055\255\041\255\057\255\000\000\022\255\
\086\255\045\255\045\255\086\255\091\255\091\255\000\000\252\254\
\000\000\000\000\000\000\086\255\046\255\055\255\086\255\086\255\
\086\255\086\255\086\255\086\255\086\255\086\255\086\255\086\255\
\086\255\086\255\086\255\086\255\042\255\048\255\047\255\000\000\
\056\255\051\255\255\254\000\000\091\255\045\255\000\000\086\255\
\000\000\000\000\000\000\055\255\050\255\052\255\000\000\056\255\
\066\255\086\255\086\255\086\255\086\255\086\255\086\255\086\255\
\086\255\070\255\086\255\086\255\080\255\081\255\082\255\055\255\
\086\255\056\255\054\255\056\255\086\255\084\255\000\000\000\000\
\088\255\055\255\055\255\087\255\056\255\090\255\092\255\093\255\
\094\255\095\255\097\255\098\255\104\255\000\000\086\255\129\255\
\000\000\000\000\000\000\000\000\000\000\000\000\045\255\124\255\
\130\255\000\000\000\000\000\000\131\255\086\255\132\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\133\255\
\000\000\000\000\045\255\000\000\000\000\000\000\086\255\000\000\
\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\134\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\135\255\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\250\254\
\000\000\000\000\000\000\000\000\136\255\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\000\000\248\255\210\255\204\255\010\000\218\255\
\000\000\223\255\000\000\005\000\000\000\240\255"

let yytablesize = 167
let yytable = "\027\000\
\031\000\071\000\019\000\034\000\035\000\029\000\001\000\095\000\
\022\000\040\000\022\000\022\000\032\000\003\000\018\000\028\000\
\060\000\036\000\099\000\104\000\074\000\075\000\037\000\038\000\
\068\000\039\000\020\000\044\000\045\000\030\000\041\000\042\000\
\043\000\108\000\076\000\079\000\103\000\064\000\082\000\083\000\
\084\000\085\000\086\000\087\000\088\000\089\000\090\000\091\000\
\092\000\093\000\094\000\126\000\102\000\128\000\046\000\081\000\
\065\000\061\000\066\000\067\000\069\000\080\000\135\000\096\000\
\097\000\098\000\100\000\132\000\040\000\106\000\127\000\101\000\
\107\000\110\000\111\000\112\000\113\000\114\000\115\000\116\000\
\117\000\109\000\119\000\120\000\118\000\105\000\021\000\022\000\
\125\000\041\000\042\000\043\000\129\000\146\000\121\000\122\000\
\123\000\023\000\024\000\025\000\130\000\026\000\131\000\134\000\
\136\000\124\000\137\000\138\000\139\000\140\000\144\000\141\000\
\142\000\153\000\006\000\007\000\133\000\008\000\143\000\009\000\
\010\000\011\000\012\000\013\000\014\000\150\000\021\000\022\000\
\047\000\048\000\049\000\050\000\051\000\052\000\053\000\054\000\
\055\000\023\000\024\000\025\000\147\000\026\000\154\000\145\000\
\148\000\149\000\000\000\152\000\151\000\000\000\047\000\038\000\
\000\000\056\000\000\000\000\000\029\000\000\000\000\000\000\000\
\000\000\000\000\000\000\057\000\000\000\058\000\059\000"

let yycheck = "\008\000\
\002\001\035\000\002\001\012\000\013\000\002\001\001\000\060\000\
\015\001\014\001\017\001\018\001\014\001\016\001\002\001\002\001\
\025\000\002\001\065\000\072\000\037\000\038\000\018\001\018\001\
\033\000\017\001\026\001\018\000\019\000\026\001\035\001\036\001\
\037\001\080\000\039\001\044\000\070\000\028\000\047\000\048\000\
\049\000\050\000\051\000\052\000\053\000\054\000\055\000\056\000\
\057\000\058\000\059\000\098\000\069\000\100\000\002\001\046\000\
\016\001\002\001\002\001\038\001\016\001\016\001\109\000\022\001\
\017\001\019\001\016\001\106\000\014\001\020\001\017\001\067\000\
\021\001\082\000\083\000\084\000\085\000\086\000\087\000\088\000\
\089\000\016\001\091\000\092\000\015\001\076\000\001\001\002\001\
\097\000\035\001\036\001\037\001\101\000\127\000\015\001\015\001\
\015\001\012\001\013\001\014\001\017\001\016\001\015\001\017\001\
\015\001\096\000\015\001\015\001\015\001\015\001\119\000\015\001\
\015\001\147\000\024\001\025\001\107\000\027\001\015\001\029\001\
\030\001\031\001\032\001\033\001\034\001\134\000\001\001\002\001\
\003\001\004\001\005\001\006\001\007\001\008\001\009\001\010\001\
\011\001\012\001\013\001\014\001\017\001\016\001\151\000\015\001\
\015\001\015\001\255\255\015\001\017\001\255\255\017\001\017\001\
\255\255\028\001\255\255\255\255\021\001\255\255\255\255\255\255\
\255\255\255\255\255\255\038\001\255\255\040\001\041\001"

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
# 21 "parser.mly"
         (_1)
# 290 "parser.ml"
               : Ast.prog))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 25 "parser.mly"
                        ( _1 )
# 297 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 28 "parser.mly"
                             ( ASTNum(_1) )
# 304 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 29 "parser.mly"
                             ( ASTId(_1) )
# 311 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 30 "parser.mly"
                             ( ASTOPrim(Ast.Add, _3, _4) )
# 319 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 31 "parser.mly"
                             ( ASTOPrim(Ast.Sub, _3, _4) )
# 327 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 32 "parser.mly"
                             ( ASTOPrim(Ast.Mul, _3, _4) )
# 335 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 33 "parser.mly"
                             ( ASTOPrim(Ast.Div, _3, _4) )
# 343 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 34 "parser.mly"
                            ( ASTOPrim(Ast.Eq, _3, _4) )
# 351 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 35 "parser.mly"
                            ( ASTOPrim(Ast.Lt, _3, _4) )
# 359 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 36 "parser.mly"
                              (ASTIf(_3,_4,_5))
# 368 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 37 "parser.mly"
                      (ASTFuncExpr(_2,_4))
# 376 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'exprs) in
    Obj.repr(
# 38 "parser.mly"
                       (ASTExprs(_2,_3))
# 384 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 39 "parser.mly"
                         ( ASTNot(Ast.Not, _3) )
# 391 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 40 "parser.mly"
                           ( ASTBPrim(Ast.And , _3,_4) )
# 399 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 41 "parser.mly"
                           ( ASTBPrim(Ast.Or, _3,_4) )
# 407 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 42 "parser.mly"
        ( ASTBool(true) )
# 413 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 43 "parser.mly"
        ( ASTBool(false) )
# 419 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 44 "parser.mly"
                     (Len(_3))
# 426 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 45 "parser.mly"
                       (Alloc(_3))
# 433 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 46 "parser.mly"
                          (ASTNth(_3,_4))
# 441 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 50 "parser.mly"
       (Expr(_1))
# 448 "parser.ml"
               : 'exprs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'exprs) in
    Obj.repr(
# 51 "parser.mly"
            (Exprs(_1,_2))
# 456 "parser.ml"
               : 'exprs))
; (fun __caml_parser_env ->
    Obj.repr(
# 55 "parser.mly"
     (TPRIM(Ast.Int))
# 462 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    Obj.repr(
# 56 "parser.mly"
      (TPRIM(Ast.Bool))
# 468 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'types) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'letype) in
    Obj.repr(
# 57 "parser.mly"
                               (TypeFunc(_2,_4))
# 476 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    Obj.repr(
# 58 "parser.mly"
      (VOID)
# 482 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'letype) in
    Obj.repr(
# 59 "parser.mly"
                      (TypeVec(_3))
# 489 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'letype) in
    Obj.repr(
# 63 "parser.mly"
          (Type(_1))
# 496 "parser.ml"
               : 'types))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'letype) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'types) in
    Obj.repr(
# 64 "parser.mly"
                     (Types(_1,_3))
# 504 "parser.ml"
               : 'types))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'letype) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 69 "parser.mly"
                          (Const(_2,_3,_4))
# 513 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'letype) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 70 "parser.mly"
                                       (Fun(_2,_3,_5,_7))
# 523 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'letype) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 71 "parser.mly"
                                           (FunRec(_3,_4,_6,_8))
# 533 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'letype) in
    Obj.repr(
# 72 "parser.mly"
                   (Var(_2,_3))
# 541 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 73 "parser.mly"
                                  (ASTProc(_2,_4,_6))
# 550 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 74 "parser.mly"
                                      (ASTProcRec(_3,_5,_7))
# 559 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'letype) in
    Obj.repr(
# 79 "parser.mly"
                      (ASTArg(_1,_3))
# 567 "parser.ml"
               : 'arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arg) in
    Obj.repr(
# 83 "parser.mly"
     (Arg(_1))
# 574 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arg) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'args) in
    Obj.repr(
# 84 "parser.mly"
                (Args(_1,_3))
# 582 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 89 "parser.mly"
       (IdentLval(_1))
# 589 "parser.ml"
               : 'lval))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'lval) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 90 "parser.mly"
                        (Nth(_3,_4))
# 597 "parser.ml"
               : 'lval))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 95 "parser.mly"
           (Echo(_2))
# 604 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'block) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 96 "parser.mly"
                          (IfProc(_2,_3,_4))
# 613 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 97 "parser.mly"
                  (ASTWhile(_2,_3))
# 621 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exprs) in
    Obj.repr(
# 98 "parser.mly"
                  (ASTCall(_2,_3))
# 629 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'lval) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 99 "parser.mly"
               (SetLval(_2,_3))
# 637 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stat) in
    Obj.repr(
# 103 "parser.mly"
      (Stats(_1))
# 644 "parser.ml"
               : 'cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'dec) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cmds) in
    Obj.repr(
# 104 "parser.mly"
                      (Dec(_1,_3))
# 652 "parser.ml"
               : 'cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'stat) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cmds) in
    Obj.repr(
# 105 "parser.mly"
                      (Stat(_1,_3))
# 660 "parser.ml"
               : 'cmds))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'cmds) in
    Obj.repr(
# 109 "parser.mly"
                (Cmds(_2))
# 667 "parser.ml"
               : 'prog))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'cmds) in
    Obj.repr(
# 113 "parser.mly"
                (CmdsBlock(_2))
# 674 "parser.ml"
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
