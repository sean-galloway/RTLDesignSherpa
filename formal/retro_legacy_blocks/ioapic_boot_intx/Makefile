# SPDX-License-Identifier: MIT
# Formal verification Makefile for ioapic_boot_intx (retro_legacy_blocks)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
#
# The companion instantiates nothing, so its closure is the module alone. Its whole contract
# -- the per-pin reroute decision and the map onto the legacy PIC inputs -- is
# combinational and at its own ports. Same shape as ioapic_lowest_pri_arb and
# ioapic_msi_emit, which are likewise dependency-free.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := ioapic_boot_intx_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/legacy-ip/retro_legacy_blocks/rtl/ioapic/filelists/ioapic_boot_intx.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: ioapic_boot_intx_flat.v
	sby -f ioapic_boot_intx.sby prove

cover: ioapic_boot_intx_flat.v
	sby -f ioapic_boot_intx.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover ioapic_boot_intx/
