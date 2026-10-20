# SPDX-License-Identifier: MIT
# Formal verification Makefile for apb4_slave_cdc
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
#
# This task used to read the RTL directly. Yosys's own SystemVerilog frontend
# cannot parse the constructs this module uses, so the proof never ran at all;
# sv2v handles them, which is the same route apb4_monitor and the wb4 family
# take. Regenerate the flat file whenever the RTL changes -- a stale flat is a
# proof about code that no longer exists.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := apb4_slave_cdc_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/amba/filelists/apb4_slave_cdc.f
# --define=FORMAL keeps the in-RTL formal blocks; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (vault/handbook/dv/formal.md).
FLAT_SV2V_FLAGS := --define=FORMAL --exclude=Assert
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: apb4_slave_cdc_flat.v
	sby -f apb4_slave_cdc.sby prove

cover: apb4_slave_cdc_flat.v
	sby -f apb4_slave_cdc.sby cover

clean:
	rm -rf apb4_slave_cdc_flat.v apb4_slave_cdc_prove apb4_slave_cdc_cover
