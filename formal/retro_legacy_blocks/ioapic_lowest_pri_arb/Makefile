# SPDX-License-Identifier: MIT
# Formal verification Makefile for ioapic_lowest_pri_arb (retro_legacy_blocks)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := ioapic_lowest_pri_arb_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/legacy-ip/retro_legacy_blocks/rtl/ioapic/filelists/ioapic_lowest_pri_arb.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: ioapic_lowest_pri_arb_flat.v
	sby -f ioapic_lowest_pri_arb.sby prove

cover: ioapic_lowest_pri_arb_flat.v
	sby -f ioapic_lowest_pri_arb.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover ioapic_lowest_pri_arb/
