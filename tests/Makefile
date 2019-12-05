default:
	$(MAKE) -C .. tests

objects := $(patsubst %,_objects/%,$(wildcard *.v) $(wildcard *.lv))

${objects}:
	$(MAKE) -C .. "tests/$@"

.PHONY: ${objects}
