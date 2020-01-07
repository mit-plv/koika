default:
	$(MAKE) -C .. examples

obj := $(patsubst %,_objects/%,$(wildcard *.v) $(wildcard *.lv))
objects := $(obj) $(patsubst %,%/,$(obj))

$(objects):
	$(MAKE) -C .. "examples/$@"

.PHONY: ${objects}
