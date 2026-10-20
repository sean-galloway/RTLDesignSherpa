# SPDX-License-Identifier: MIT
# Formal verification Makefile for ioapic_deliv_merge (retro_legacy_blocks)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
#
# That drift is not hypothetical. An earlier version of this file crammed all
# three sources into DUT and omitted arbiter_priority_encoder, and yosys
# stopped with "Module `\arbiter_priority_encoder' referenced in module
# `\arbiter_round_robin' ... is not part of the design". The same omission also
# made a lint waiver read as non-load-bearing, because the arbiter never
# elaborated -- one mistake, two symptoms that looked unrelated.
#
REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := ioapic_deliv_merge_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/legacy-ip/retro_legacy_blocks/rtl/ioapic/filelists/ioapic_deliv_merge.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: ioapic_deliv_merge_flat.v
	sby -f ioapic_deliv_merge.sby prove

cover: ioapic_deliv_merge_flat.v
	sby -f ioapic_deliv_merge.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover ioapic_deliv_merge/
