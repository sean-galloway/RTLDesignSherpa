# SPDX-License-Identifier: MIT
# Formal verification Makefile for wb4_slave_cdc
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
# (same shape as formal/amba/wb4_master/Makefile).

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := wb4_slave_cdc_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/amba/filelists/wb4_slave_cdc.f
# --define=FORMAL keeps the in-RTL formal blocks; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (vault/handbook/dv/formal.md).
FLAT_SV2V_FLAGS := --define=FORMAL --exclude=Assert
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: wb4_slave_cdc_flat.v
	sby -f wb4_slave_cdc.sby prove

cover: wb4_slave_cdc_flat.v
	sby -f wb4_slave_cdc.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
