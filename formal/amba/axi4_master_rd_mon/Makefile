# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi4_master_rd_mon
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := axi4_master_rd_mon_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/amba/filelists/axi4_master_rd_mon.f
# --define=FORMAL keeps the in-RTL formal blocks; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (vault/handbook/dv/formal.md).
FLAT_SV2V_FLAGS := --define=FORMAL --exclude=Assert
# ocelus_pkg re-exports its sub-packages' types, which trips sv2v's
# "ambiguous identifier"; the prep strips the import and the scope prefix.
FLAT_PREP       := s/import ocelus_pkg::\*;//g;s/ocelus_pkg:://g
# Wrapper gating properties, spliced before endmodule of axi4_master_rd_mon.sv (the
# RTL carries no assertions).
FLAT_SPLICE      := $(REPO_ROOT)/formal/amba/axi4_master_rd_mon/axi4_master_rd_mon_props.svh
FLAT_SPLICE_INTO := axi4_master_rd_mon.sv
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean

prove: axi4_master_rd_mon_flat.v
	sby -f axi4_master_rd_mon.sby prove

cover: axi4_master_rd_mon_flat.v
	sby -f axi4_master_rd_mon.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
