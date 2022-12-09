open Ast
open Lexing


let rec print_expr e =
    match e with
    | Id(v) -> Printf.printf "%s" v
    | Cste(c) -> Printf.printf "%d" c
    | UMinus(e) -> (Printf.printf "-"; print_expr e)
    | Plus(e1,e2) -> (Printf.printf "("; print_expr e1; Printf.printf " + "; print_expr e2; Printf.printf ")")
    | Minus(e1,e2) -> (Printf.printf "("; print_expr e1; Printf.printf " - "; print_expr e2; Printf.printf ")")
    | Times(e1,e2) -> (Printf.printf "("; print_expr e1; Printf.printf " * "; print_expr e2; Printf.printf ")")
    | Div(e1,e2) -> (Printf.printf "("; print_expr e1; Printf.printf " / "; print_expr e2; Printf.printf ")")
    | Ite(c,e1,e2) -> (Printf.printf "(if "; print_cond c; Printf.printf " then "; print_expr e1;
                      Printf.printf " else "; print_expr e2; Printf.printf ")")
and print_cond e =
    match e with
    | COMP(e1, op, e2) -> (Printf.printf "("; print_expr e1;
    (match op with
     | Eq -> Printf.printf " == "
     | Neq -> Printf.printf " != "
     | Lt -> Printf.printf " < "
     | Le -> Printf.printf " <= "
     | Gt -> Printf.printf " > "
     | Ge -> Printf.printf " >="
    ); print_expr e2; Printf.printf ")")
    | AND(c1, c2) -> (Printf.printf "("; print_cond c1; Printf.printf " && "; print_cond c2; Printf.printf ")")
    | OR (c1, c2) -> (Printf.printf "("; print_cond c1; Printf.printf " || "; print_cond c2; Printf.printf ")")
    | NOT(c) -> (Printf.printf "!"; print_cond c)

let print_decl d =
    Printf.printf "%s := " (fst d);
    print_expr (snd d);
    Printf.printf ";\n"

let rec print_decl_list l =
    match l with V(s, r) -> (print_decl s; print_decl_list r)
    | N -> ()

let print_ast prog =
    print_decl_list (fst prog);
    Printf.printf "begin\n  ";
    print_expr (snd prog);
    Printf.printf "\nend\n"


(* lexbuf: correspond au buffer d'entrée associé au programme qu'on traite
 * file_in: descripteur de fichier pour ce programme
 * chan: descripteur de fichier dans lequel on ecrit le code produit pour la
 *       partie compilation. Par défaut le code ira dans le fichier out.txt
 *)
let parse_with_error lexbuf file_in chan =
  let print_position outx lexbuf =
    let pos = lexbuf.lex_curr_p in
    Printf.fprintf outx "%s:%d:%d" file_in
      pos.pos_lnum (pos.pos_cnum - pos.pos_bol + 1)
  in
  try
    (* lance l'analyse syntaxique (qui appellera l'analyse lexicale) en
     * executant au fur et à mesure les actions associées aux productions.
     * L'appel est fait par TpParse.prog (où prog est le non-terminal déclaré
     * comme axiome dans tpParse.mly). 
     * La valeur retournée par la production qui définit l'axiome renvoie une
     * valeur du type progType à définir dans ast.ml.
     *)
    let ast = TpParse.prog TpLex.token lexbuf in
    print_string "Fin de l'analyse syntaxique";
    print_newline ();
    print_ast ast
  with (* traite exception général ... *)
    TpParse.Error -> (* levée par l'analyseur syntaxique *)
    Printf.fprintf stderr "Syntax error at position %a\n" print_position lexbuf;
    exit (-1)
  | VC_Error msg ->
     Printf.fprintf stderr "Erreur contextuelle: %s\n" msg;
     exit (-1)
  | RUN_Error msg -> (* uniquement pour la version interprete *)
     Printf.fprintf stderr "Erreur à l'execution: %s\n" msg;
     exit (-1)
  | MISC_Error msg -> (* pour l'instant juste erreur lexicale *)
     Printf.fprintf stderr "Error: %s\n" msg;
     exit (-1)

let _ =
  let argc = Array.length Sys.argv in
  if argc = 1 then
    print_endline "usage: tp programme [fichier-pour-le-code] "
  else
    begin
      (* si on ne passe pas à l'appel le nom du fichier dans lequel
       * ecrire le code produit, on utilise par défaut le fichier "out.txt"
       *)
      let file_out = if argc = 3 then Sys.argv.(2) else "out.txt"
      and file_in = Sys.argv.(1) in
      let chan_in = open_in file_in
      and chan_out = open_out file_out in
      let lexbuf = Lexing.from_channel chan_in
      in
      parse_with_error lexbuf file_in chan_out;
      close_in chan_in;
      close_out chan_out
    end
