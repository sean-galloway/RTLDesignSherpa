# SPDX-License-Identifier: MIT
# Formal verification Makefile for ioapic_msi_emit (retro_legacy_blocks)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
#
# The emitter instantiates nothing. Its entire contract -- the MSI format
# mapping and the command packing -- is combinational and at its own ports.
# Its filelist also carries apb4_master_stub's closure (the integration needs
# it); nothing here instantiates those modules, so elaboration drops them and
# the proof is of the emitter alone, not the master. Same shape as
# ioapic_lowest_pri_arb, which is likewise dependency-free.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := ioapic_msi_emit_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/legacy-ip/retro_legacy_blocks/rtl/ioapic/filelists/ioapic_msi_emit.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: ioapic_msi_emit_flat.v
	sby -f ioapic_msi_emit.sby prove

cover: ioapic_msi_emit_flat.v
	sby -f ioapic_msi_emit.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover ioapic_msi_emit/
