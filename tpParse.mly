%{
open Ast
%}
%token <string> ID
%token <int> CSTE
%token <Ast.opComp> RELOP
%token PLUS MINUS TIMES DIV UMINUS UPLUS
%token LPAREN RPAREN SEMICOLON
%token ASSIGN
%token IF THEN ELSE BEGIN END
%token AND OR NOT
%token EOF

%type <expType> expr
%type <compType> cond
%type <declType> decl
%type <declListType> declarations

%left ELSE
%left OR
%left AND
%left PLUS MINUS
%left TIMES DIV
%right NOT UMINUS UPLUS

(* l'axiome est aussi le nom de la fonction a appeler pour faire l'analyse 
 * syntaxique
 *)
%start<Ast.progType> prog
%%
prog:  d = declarations BEGIN e = expr END EOF { (d, e) }

declarations : (* a faire *)
    d = decl l = declarations { V(d, l) }
  | { N }


decl:
    id = ID ASSIGN e = expr SEMICOLON  { (id, e) }

cond:
    el = expr ro = RELOP er = expr { COMP(el, ro, er) }
  | cl = cond AND cr = cond        { AND(cl, cr) }
  | cl = cond OR cr = cond         { OR(cl, cr)  }
  | NOT c = cond                   { NOT(c)      }
  | c = delimited (LPAREN, cond, RPAREN) { c }

expr: (* a completer *)
    x = ID 		 { Id(x) }
  | v = CSTE		 { Cste(v) }
  | el = expr PLUS  er = expr { Plus (el, er) }
  | el = expr TIMES er = expr { Times(el, er) }
  | el = expr MINUS er = expr { Minus(el, er) }
  | el = expr DIV   er = expr { Div  (el, er) }
  | MINUS e = expr %prec UMINUS { UMinus(e) }
  | PLUS e = expr %prec UPLUS { e }
  //| UMINUS expr { }
  | IF c = cond THEN t = expr ELSE e = expr { Ite(c, t, e) }
  | e = delimited (LPAREN, expr, RPAREN) { e }
