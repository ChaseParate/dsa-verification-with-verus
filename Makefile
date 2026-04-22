VERUS := verus
VERUSFMT := verusfmt

SOURCE_DIRECTORY := ./src

ROOT_SOURCE_FILE := $(SOURCE_DIRECTORY)/main.rs
ALL_SOURCE_FILES := $(shell find $(SOURCE_DIRECTORY) -name "*.rs")

.PHONY: check format

check:
	$(VERUS) $(ROOT_SOURCE_FILE) --no-cheating

format:
	$(VERUSFMT) $(ALL_SOURCE_FILES)
