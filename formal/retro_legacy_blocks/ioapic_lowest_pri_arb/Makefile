# SPDX-License-Identifier: MIT
# Formal verification Makefile for ioapic_lowest_pri_arb (retro_legacy_blocks)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes
DUT := $(REPO_ROOT)/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_lowest_pri_arb.sv

.PHONY: prove cover all clean

all: prove cover

prove: ioapic_lowest_pri_arb_flat.v
	sby -f ioapic_lowest_pri_arb.sby prove

cover: ioapic_lowest_pri_arb_flat.v
	sby -f ioapic_lowest_pri_arb.sby cover

ioapic_lowest_pri_arb_flat.v: $(DUT)
	$(SV2V) $(INC) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover ioapic_lowest_pri_arb/
