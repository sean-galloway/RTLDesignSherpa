REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := axi4_to_apb4_convert_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/utility-ip/converters/rtl/filelists/axi4_to_apb4_convert.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: axi4_to_apb4_convert_flat.v
	sby -f axi4_to_apb4_convert.sby prove

cover: axi4_to_apb4_convert_flat.v
	sby -f axi4_to_apb4_convert.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover

.PHONY: prove cover clean
