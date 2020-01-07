default:
	$(MAKE) -C .. tests

obj := $(patsubst %,_objects/%,$(wildcard *.v) $(wildcard *.lv))
objects := $(obj) $(patsubst %,%/,$(obj))

$(objects):
	$(MAKE) -C .. "tests/$@"

.PHONY: $(objects)
