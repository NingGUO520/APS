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
\009\000\009\000\009\000\009\000\009\000\009\000\011\000\005\000\
\005\000\012\000\012\000\013\000\013\000\013\000\013\000\013\000\
\014\000\015\000\015\000\015\000\015\000\003\000\010\000\000\000"

let yylen = "\002\000\
\001\000\001\000\001\000\001\000\005\000\005\000\005\000\005\000\
\005\000\005\000\006\000\004\000\004\000\004\000\005\000\005\000\
\001\000\001\000\004\000\004\000\005\000\001\000\002\000\001\000\
\001\000\005\000\001\000\004\000\001\000\003\000\004\000\007\000\
\008\000\003\000\006\000\007\000\007\000\008\000\003\000\001\000\
\003\000\001\000\005\000\002\000\004\000\003\000\003\000\003\000\
\002\000\001\000\003\000\003\000\001\000\003\000\003\000\002\000"

let yydefred = "\000\000\
\000\000\000\000\000\000\056\000\001\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\053\000\000\000\000\000\000\000\000\000\003\000\004\000\
\017\000\018\000\000\000\000\000\044\000\000\000\000\000\000\000\
\042\000\000\000\000\000\000\000\000\000\000\000\049\000\000\000\
\000\000\054\000\000\000\025\000\024\000\027\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\034\000\000\000\000\000\000\000\048\000\000\000\
\000\000\046\000\000\000\047\000\051\000\052\000\000\000\000\000\
\000\000\031\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\045\000\023\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\014\000\000\000\000\000\019\000\020\000\013\000\039\000\012\000\
\041\000\000\000\000\000\000\000\055\000\028\000\030\000\000\000\
\000\000\000\000\005\000\006\000\007\000\008\000\010\000\009\000\
\015\000\016\000\000\000\021\000\035\000\000\000\043\000\026\000\
\000\000\032\000\037\000\000\000\011\000\036\000\033\000\038\000"

let yydgoto = "\002\000\
\004\000\000\000\005\000\075\000\065\000\076\000\080\000\081\000\
\016\000\073\000\066\000\035\000\017\000\018\000\105\000"

let yysindex = "\007\000\
\249\254\000\000\122\255\000\000\000\000\011\255\008\255\059\255\
\012\255\033\255\001\255\059\255\059\255\014\255\059\255\002\255\
\018\255\000\000\000\255\062\255\062\255\054\255\000\000\000\000\
\000\000\000\000\129\255\056\255\000\000\062\255\048\255\067\255\
\000\000\036\255\059\255\072\255\072\255\059\255\000\000\122\255\
\122\255\000\000\071\255\000\000\000\000\000\000\059\255\073\255\
\062\255\059\255\059\255\059\255\059\255\059\255\059\255\059\255\
\059\255\059\255\059\255\059\255\059\255\059\255\059\255\069\255\
\076\255\075\255\000\000\056\255\084\255\001\255\000\000\122\255\
\072\255\000\000\059\255\000\000\000\000\000\000\062\255\083\255\
\088\255\000\000\056\255\089\255\059\255\059\255\059\255\059\255\
\059\255\059\255\059\255\059\255\098\255\059\255\059\255\101\255\
\102\255\103\255\062\255\059\255\056\255\087\255\056\255\059\255\
\108\255\000\000\000\000\104\255\062\255\062\255\111\255\056\255\
\105\255\112\255\135\255\143\255\144\255\145\255\146\255\147\255\
\000\000\059\255\148\255\000\000\000\000\000\000\000\000\000\000\
\000\000\072\255\127\255\150\255\000\000\000\000\000\000\151\255\
\110\255\154\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\153\255\000\000\000\000\072\255\000\000\000\000\
\255\254\000\000\000\000\110\255\000\000\000\000\000\000\000\000"

let yyrindex = "\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\155\255\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\156\255\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\050\255\000\000\000\000\000\000\000\000\157\255\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\
\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000\000"

let yygindex = "\000\000\
\000\000\000\000\000\000\248\255\210\255\199\255\247\255\065\000\
\000\000\221\255\000\000\105\000\000\000\000\000\022\000"

let yytablesize = 178
let yytable = "\029\000\
\064\000\074\000\033\000\036\000\037\000\098\000\039\000\001\000\
\003\000\021\000\047\000\048\000\020\000\030\000\034\000\038\000\
\042\000\107\000\063\000\040\000\067\000\102\000\006\000\007\000\
\019\000\008\000\071\000\009\000\010\000\011\000\012\000\013\000\
\014\000\022\000\031\000\041\000\111\000\106\000\082\000\084\000\
\015\000\085\000\086\000\087\000\088\000\089\000\090\000\091\000\
\092\000\093\000\094\000\095\000\096\000\097\000\129\000\049\000\
\131\000\064\000\032\000\023\000\024\000\077\000\078\000\068\000\
\022\000\138\000\022\000\022\000\069\000\108\000\025\000\026\000\
\027\000\070\000\028\000\043\000\113\000\114\000\115\000\116\000\
\117\000\118\000\119\000\120\000\043\000\122\000\123\000\072\000\
\083\000\127\000\099\000\128\000\100\000\101\000\149\000\132\000\
\044\000\045\000\046\000\103\000\136\000\155\000\109\000\130\000\
\112\000\044\000\045\000\046\000\110\000\079\000\023\000\024\000\
\121\000\147\000\158\000\124\000\125\000\126\000\134\000\139\000\
\160\000\025\000\026\000\027\000\133\000\153\000\140\000\137\000\
\154\000\023\000\024\000\050\000\051\000\052\000\053\000\054\000\
\055\000\056\000\057\000\058\000\025\000\026\000\027\000\150\000\
\028\000\006\000\007\000\159\000\008\000\141\000\009\000\010\000\
\011\000\012\000\013\000\014\000\059\000\142\000\143\000\144\000\
\145\000\146\000\148\000\015\000\151\000\152\000\060\000\157\000\
\061\000\062\000\156\000\050\000\040\000\135\000\104\000\000\000\
\000\000\029\000"

let yycheck = "\008\000\
\002\001\037\000\002\001\012\000\013\000\063\000\015\000\001\000\
\016\001\002\001\020\000\021\000\002\001\002\001\014\001\002\001\
\017\001\075\000\027\000\018\001\030\000\068\000\024\001\025\001\
\003\000\027\001\035\000\029\001\030\001\031\001\032\001\033\001\
\034\001\026\001\002\001\018\001\083\000\073\000\047\000\049\000\
\042\001\050\000\051\000\052\000\053\000\054\000\055\000\056\000\
\057\000\058\000\059\000\060\000\061\000\062\000\101\000\002\001\
\103\000\002\001\026\001\001\001\002\001\040\000\041\000\016\001\
\015\001\112\000\017\001\018\001\002\001\079\000\012\001\013\001\
\014\001\038\001\016\001\014\001\085\000\086\000\087\000\088\000\
\089\000\090\000\091\000\092\000\014\001\094\000\095\000\016\001\
\016\001\099\000\022\001\100\000\017\001\019\001\130\000\104\000\
\035\001\036\001\037\001\016\001\110\000\137\000\020\001\017\001\
\016\001\035\001\036\001\037\001\021\001\039\001\001\001\002\001\
\015\001\122\000\150\000\015\001\015\001\015\001\015\001\015\001\
\156\000\012\001\013\001\014\001\017\001\016\001\015\001\017\001\
\137\000\001\001\002\001\003\001\004\001\005\001\006\001\007\001\
\008\001\009\001\010\001\011\001\012\001\013\001\014\001\017\001\
\016\001\024\001\025\001\156\000\027\001\015\001\029\001\030\001\
\031\001\032\001\033\001\034\001\028\001\015\001\015\001\015\001\
\015\001\015\001\015\001\042\001\015\001\015\001\038\001\015\001\
\040\001\041\001\017\001\017\001\017\001\109\000\070\000\255\255\
\255\255\021\001"

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
# 297 "parser.ml"
               : Ast.prog))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 26 "parser.mly"
                        ( _1 )
# 304 "parser.ml"
               : Ast.expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : int) in
    Obj.repr(
# 29 "parser.mly"
                             ( ASTNum(_1) )
# 311 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 30 "parser.mly"
                             ( ASTId(_1) )
# 318 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 31 "parser.mly"
                             ( ASTOPrim(Ast.Add, _3, _4) )
# 326 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 32 "parser.mly"
                             ( ASTOPrim(Ast.Sub, _3, _4) )
# 334 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 33 "parser.mly"
                             ( ASTOPrim(Ast.Mul, _3, _4) )
# 342 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 34 "parser.mly"
                             ( ASTOPrim(Ast.Div, _3, _4) )
# 350 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 35 "parser.mly"
                            ( ASTOPrim(Ast.Eq, _3, _4) )
# 358 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 36 "parser.mly"
                            ( ASTOPrim(Ast.Lt, _3, _4) )
# 366 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 3 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _5 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 37 "parser.mly"
                              (ASTIf(_3,_4,_5))
# 375 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 38 "parser.mly"
                      (ASTFuncExpr(_2,_4))
# 383 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'exprs) in
    Obj.repr(
# 39 "parser.mly"
                       (ASTExprs(_2,_3))
# 391 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 40 "parser.mly"
                         ( ASTNot(Ast.Not, _3) )
# 398 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 41 "parser.mly"
                           ( ASTBPrim(Ast.And , _3,_4) )
# 406 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 42 "parser.mly"
                           ( ASTBPrim(Ast.Or, _3,_4) )
# 414 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 43 "parser.mly"
        ( ASTBool(true) )
# 420 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    Obj.repr(
# 44 "parser.mly"
        ( ASTBool(false) )
# 426 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 45 "parser.mly"
                     (Len(_3))
# 433 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 46 "parser.mly"
                       (Alloc(_3))
# 440 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 47 "parser.mly"
                          (ASTNth(_3,_4))
# 448 "parser.ml"
               : 'expr))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 51 "parser.mly"
       (Expr(_1))
# 455 "parser.ml"
               : 'exprs))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'exprs) in
    Obj.repr(
# 52 "parser.mly"
            (Exprs(_1,_2))
# 463 "parser.ml"
               : 'exprs))
; (fun __caml_parser_env ->
    Obj.repr(
# 56 "parser.mly"
     (TPRIM(Ast.Int))
# 469 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    Obj.repr(
# 57 "parser.mly"
      (TPRIM(Ast.Bool))
# 475 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 3 : 'types) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'letype) in
    Obj.repr(
# 58 "parser.mly"
                               (TypeFunc(_2,_4))
# 483 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    Obj.repr(
# 59 "parser.mly"
      (VOID)
# 489 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'letype) in
    Obj.repr(
# 60 "parser.mly"
                      (TypeVec(_3))
# 496 "parser.ml"
               : 'letype))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'letype) in
    Obj.repr(
# 64 "parser.mly"
          (Type(_1))
# 503 "parser.ml"
               : 'types))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'letype) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'types) in
    Obj.repr(
# 65 "parser.mly"
                     (Types(_1,_3))
# 511 "parser.ml"
               : 'types))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'letype) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 70 "parser.mly"
                          (Const(_2,_3,_4))
# 520 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'letype) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 71 "parser.mly"
                                        (Fun(_2,_3,_5,_7))
# 530 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'letype) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 72 "parser.mly"
                                           (FunRec(_3,_4,_6,_8))
# 540 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'letype) in
    Obj.repr(
# 73 "parser.mly"
                   (Var(_2,_3))
# 548 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _6 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 74 "parser.mly"
                                  (ASTProc(_2,_4,_6))
# 557 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 4 : string) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 75 "parser.mly"
                                      (ASTProcRec(_3,_5,_7))
# 566 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 4 : 'letype) in
    let _5 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _7 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 76 "parser.mly"
                                         (FunPro(_2,_3,_5,_7))
# 576 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 5 : string) in
    let _4 = (Parsing.peek_val __caml_parser_env 4 : 'letype) in
    let _6 = (Parsing.peek_val __caml_parser_env 2 : 'args) in
    let _8 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 77 "parser.mly"
                                             (FunProRec(_3,_4,_6,_8))
# 586 "parser.ml"
               : 'dec))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'letype) in
    Obj.repr(
# 82 "parser.mly"
                      (ASTArg(_1,_3))
# 594 "parser.ml"
               : 'arg))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'arg) in
    Obj.repr(
# 86 "parser.mly"
     (Arg(_1))
# 601 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'arg) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'args) in
    Obj.repr(
# 87 "parser.mly"
                (Args(_1,_3))
# 609 "parser.ml"
               : 'args))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : string) in
    Obj.repr(
# 92 "parser.mly"
       (IdentLval(_1))
# 616 "parser.ml"
               : 'lval))
; (fun __caml_parser_env ->
    let _3 = (Parsing.peek_val __caml_parser_env 2 : 'lval) in
    let _4 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    Obj.repr(
# 93 "parser.mly"
                        (Nth(_3,_4))
# 624 "parser.ml"
               : 'lval))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 98 "parser.mly"
           (Echo(_2))
# 631 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 2 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 1 : 'block) in
    let _4 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 99 "parser.mly"
                          (IfProc(_2,_3,_4))
# 640 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'expr) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'block) in
    Obj.repr(
# 100 "parser.mly"
                  (ASTWhile(_2,_3))
# 648 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : string) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'exprs) in
    Obj.repr(
# 101 "parser.mly"
                  (ASTCall(_2,_3))
# 656 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'lval) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 102 "parser.mly"
               (SetLval(_2,_3))
# 664 "parser.ml"
               : 'stat))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 0 : 'expr) in
    Obj.repr(
# 106 "parser.mly"
             (Return(_2))
# 671 "parser.ml"
               : 'ret))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'stat) in
    Obj.repr(
# 110 "parser.mly"
      (Stats(_1))
# 678 "parser.ml"
               : 'cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'dec) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cmds) in
    Obj.repr(
# 111 "parser.mly"
                      (Dec(_1,_3))
# 686 "parser.ml"
               : 'cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 2 : 'stat) in
    let _3 = (Parsing.peek_val __caml_parser_env 0 : 'cmds) in
    Obj.repr(
# 112 "parser.mly"
                      (Stat(_1,_3))
# 694 "parser.ml"
               : 'cmds))
; (fun __caml_parser_env ->
    let _1 = (Parsing.peek_val __caml_parser_env 0 : 'ret) in
    Obj.repr(
# 113 "parser.mly"
     (Ret(_1))
# 701 "parser.ml"
               : 'cmds))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'cmds) in
    Obj.repr(
# 117 "parser.mly"
                (Cmds(_2))
# 708 "parser.ml"
               : 'prog))
; (fun __caml_parser_env ->
    let _2 = (Parsing.peek_val __caml_parser_env 1 : 'cmds) in
    Obj.repr(
# 121 "parser.mly"
                (CmdsBlock(_2))
# 715 "parser.ml"
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
