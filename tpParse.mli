
(* The type of tokens. *)

type token = 
  | UPLUS
  | UMINUS
  | TIMES
  | THEN
  | SEMICOLON
  | RPAREN
  | RELOP of (Ast.opComp)
  | PLUS
  | OR
  | NOT
  | MINUS
  | LPAREN
  | IF
  | ID of (string)
  | EOF
  | END
  | ELSE
  | DIV
  | CSTE of (int)
  | BEGIN
  | ASSIGN
  | AND

(* This exception is raised by the monolithic API functions. *)

exception Error

(* The monolithic API. *)

val prog: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Ast.progType)
