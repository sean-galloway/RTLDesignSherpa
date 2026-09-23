# SPDX-License-Identifier: MIT
# Formal verification Makefile for ioapic_boot_intx (retro_legacy_blocks)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
#
# No DEPS and no PKGS: the companion instantiates nothing. Its whole contract
# -- the per-pin reroute decision and the map onto the legacy PIC inputs -- is
# combinational and at its own ports. Same shape as ioapic_lowest_pri_arb and
# ioapic_msi_emit, which are likewise dependency-free.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes
DUT := $(REPO_ROOT)/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_boot_intx.sv

.PHONY: prove cover all clean

all: prove cover

prove: ioapic_boot_intx_flat.v
	sby -f ioapic_boot_intx.sby prove

cover: ioapic_boot_intx_flat.v
	sby -f ioapic_boot_intx.sby cover

ioapic_boot_intx_flat.v: $(DUT)
	$(SV2V) $(INC) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover ioapic_boot_intx/
