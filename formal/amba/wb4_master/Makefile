# SPDX-License-Identifier: MIT
# Formal verification Makefile for wb4_master
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := wb4_master_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/amba/filelists/wb4_master.f
# --define=FORMAL keeps the in-RTL formal blocks; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (vault/handbook/dv/formal.md).
FLAT_SV2V_FLAGS := --define=FORMAL --exclude=Assert
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover prove_classic cover_classic all clean

all: prove cover prove_classic cover_classic

prove: wb4_master_flat.v
	sby -f wb4_master.sby prove

cover: wb4_master_flat.v
	sby -f wb4_master.sby cover

# CLASSIC=1 (B4 standard mode) via chparam on the harness top.
prove_classic: wb4_master_flat.v
	sby -f wb4_master.sby prove_classic

cover_classic: wb4_master_flat.v
	sby -f wb4_master.sby cover_classic

clean:
	rm -rf *_flat.v *_prove *_cover *_prove_classic *_cover_classic
