.PHONY: all clean

AGDA_FLAGS := -i. --safe +RTS -M6G -A128M -RTS
BUILD_DIR := _build/$(shell agda --numeric-version)/agda

$(BUILD_DIR)/index.agdai: index.agda
	agda $(AGDA_FLAGS) $<

clean:
	rm -rf _build/
