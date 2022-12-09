INTERFACES = tpParse.mli
SOURCES    = ast.ml tpParse.ml tpLex.ml misc.ml main.ml
#GENERATED  = tpLex.ml tpParse.ml tpParse.mli tpParse.automaton tpParse.conflicts
GENERATED  = tpParse.ml tpParse.mli tpParse.automaton tpParse.conflicts

tp: tpParse.mli $(SOURCES)
	ocamlc -c ast.ml
	ocamlc $(INTERFACES)
	ocamlc -o tp $(SOURCES)

testLex : tpParse.mli tpLex.ml testLex.ml ast.mli
	ocamlc -c ast.ml
	ocamlc $(INTERFACES)
	ocamlc -o testLex ast.ml misc.ml tpParse.ml  tpLex.ml testLex.ml

ast.mli: ast.ml
	ocamlc -c ast.ml

tpLex.ml: tpLex.mll tpParse.mli ast.ml
	ocamllex tpLex.mll

tpParse.mli : tpParse.mly ast.mli
	menhir --dump --explain --infer tpParse.mly
#	menhir --dump --explain --strict --infer tpParse.mly

clean:
	rm -rf  tp testLex *.o *.cmi *.cmo *.cmx *~ $(GENERATED) out.txt
