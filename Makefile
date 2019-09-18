default:
	rm -f _build/default/Extraction.vo
	dune build Extraction.vo
	cp _build/default/SGA.ml* ocaml

all:
	dune build $(patsubst %.v,%.vo,$(wildcard *.v))

clean:
	dune clean
