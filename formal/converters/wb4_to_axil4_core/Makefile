# SPDX-License-Identifier: MIT
# Formal verification Makefile for wb4_to_axil4_core
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog (the
# core imports wb4_pkg and uses the reset_defs macros, which the plain
# `read -sv` flow of the other converters harnesses does not need).

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := wb4_to_axil4_core_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/utility-ip/converters/rtl/filelists/wb4_to_axil4_core.f
# --define=FORMAL keeps the in-RTL formal blocks; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (vault/handbook/dv/formal.md).
FLAT_SV2V_FLAGS := --define=FORMAL --exclude=Assert
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: wb4_to_axil4_core_flat.v
	sby -f wb4_to_axil4_core.sby prove

cover: wb4_to_axil4_core_flat.v
	sby -f wb4_to_axil4_core.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
