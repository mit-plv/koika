sv_files := $(wildcard *.sv)
v_files := memory.v

%.v: %.sv $(sv_files) Makefile
	/build/sv2v/bin/sv2v "$<" > "$@"

default: $(v_files);
