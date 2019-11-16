default:
	$(MAKE) -C .. tests

OBJECTS := $(wildcard *.objects/)

${OBJECTS}:
	$(MAKE) -C .. "tests/$@"

.PHONY: ${OBJECTS}
