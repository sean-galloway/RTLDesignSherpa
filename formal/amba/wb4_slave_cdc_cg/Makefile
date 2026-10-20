# SPDX-License-Identifier: MIT
# Formal verification Makefile for wb4_slave_cdc_cg
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
#
# This block had NO proof until 2026-09-11, while every APB family proved all
# three of <x>_slave_cdc, <x>_slave_cg and <x>_slave_cdc_cg. The gap was in no
# tracker, so nothing surfaced it.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := wb4_slave_cdc_cg_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/amba/filelists/wb4_slave_cdc_cg.f
# --define=FORMAL keeps the in-RTL formal blocks; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (vault/handbook/dv/formal.md).
FLAT_SV2V_FLAGS := --define=FORMAL --exclude=Assert
# The harness defines its own copy of these modules (a clock-enable model of
# the ICG cell: a derived clock is not provable in this flow).
FLAT_EXCLUDE    := /icg.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: wb4_slave_cdc_cg_flat.v
	sby -f wb4_slave_cdc_cg.sby prove

cover: wb4_slave_cdc_cg_flat.v
	sby -f wb4_slave_cdc_cg.sby cover

clean:
	rm -rf wb4_slave_cdc_cg_flat.v wb4_slave_cdc_cg_prove wb4_slave_cdc_cg_cover
