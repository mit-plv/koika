default:
	$(MAKE) -C .. tests

objects := $(patsubst %,_objects/%,$(wildcard *.v) $(wildcard *.lv))

${objects}/ ${objects}:
	$(MAKE) -C .. "tests/$@"

.PHONY: ${objects}
