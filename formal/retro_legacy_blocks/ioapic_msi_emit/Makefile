# SPDX-License-Identifier: MIT
# Formal verification Makefile for ioapic_msi_emit (retro_legacy_blocks)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
#
# No DEPS and no PKGS: the emitter instantiates nothing. Its entire contract --
# the MSI format mapping and the command packing -- is combinational and at its
# own ports, so apb4_master_stub's closure (counter_bin, counter_load_clear,
# fifo_control, gaxi_fifo_sync, gaxi_skid_buffer, apb4_master) is deliberately
# NOT pulled in: that would prove the master, not the emitter. Same shape as
# ioapic_lowest_pri_arb, which is likewise dependency-free.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes
DUT := $(REPO_ROOT)/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_msi_emit.sv

.PHONY: prove cover all clean

all: prove cover

prove: ioapic_msi_emit_flat.v
	sby -f ioapic_msi_emit.sby prove

cover: ioapic_msi_emit_flat.v
	sby -f ioapic_msi_emit.sby cover

ioapic_msi_emit_flat.v: $(DUT)
	$(SV2V) $(INC) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover ioapic_msi_emit/
