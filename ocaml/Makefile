driver.exe:
	rm -f driver.exe
	dune build driver.exe
	cp ../_build/default/ocaml/driver.exe .

dot: driver.exe
	./driver.exe | tee /dev/stderr | tee circuit.dot | dot -Tpng -o circuit.png
