# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi4_master_rd_mon_cg
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
#
# This block had NO proof until 2026-09-11 (TASK-090). Its KNOWN_LIMITATION.md
# said the proof was blocked by a multi-driver issue in axi_monitor_trans_mgr
# and by two clock-gating bugs in the wrapper; all three were fixed, and the
# page was left claiming a block that no longer existed.
#
# The flat is the closure of axi4_master_rd_mon plus the clock gate, with icg.f
# DELIBERATELY EXCLUDED (FLAT_EXCLUDE) -- the harness supplies
# a clock-enable model of the cell, because a derived clock is not provable in
# this flow. See formal/amba/wb4_slave_cdc_cg for the same arrangement.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := axi4_master_rd_mon_cg_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/amba/filelists/axi4_master_rd_mon_cg.f
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
# The harness defines its own copy of these modules (a clock-enable model of
# the ICG cell: a derived clock is not provable in this flow).
FLAT_EXCLUDE    := /icg.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: axi4_master_rd_mon_cg_flat.v
	sby -f axi4_master_rd_mon_cg.sby prove

cover: axi4_master_rd_mon_cg_flat.v
	sby -f axi4_master_rd_mon_cg.sby cover

clean:
	rm -rf axi4_master_rd_mon_cg_flat.v axi4_master_rd_mon_cg_prove axi4_master_rd_mon_cg_cover
