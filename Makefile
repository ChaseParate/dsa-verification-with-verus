VERUS := verus

SOURCE_DIRECTORY := ./src

.PHONY: check

check:
	$(VERUS) $(SOURCE_DIRECTORY)/main.rs
