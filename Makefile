default:
	rm -f _build/default/Extraction.vo
	dune build Extraction.vo
	cp _build/default/SGA.ml* ocaml
