# sv2v preprocessing for counter_freq_invariant
# Yosys can't parse SV function return statements
REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := counter_freq_invariant_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/common/filelists/counter_freq_invariant.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean

prove: counter_freq_invariant_flat.v
	sby -f counter_freq_invariant.sby prove

cover: counter_freq_invariant_flat.v
	sby -f counter_freq_invariant.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
