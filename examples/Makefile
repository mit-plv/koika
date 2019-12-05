default:
	$(MAKE) -C .. examples

objects := $(patsubst %,_objects/%,$(wildcard *.v) $(wildcard *.lv))

${objects}:
	$(MAKE) -C .. "examples/$@"

.PHONY: ${objects}
