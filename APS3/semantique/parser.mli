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

val program :
  (Lexing.lexbuf  -> token) -> Lexing.lexbuf -> Ast.prog
