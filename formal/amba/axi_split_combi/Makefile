# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi_split_combi
# Workflow: sv2v flattens the REAL RTL -> sby reads plain Verilog (plain prep).
#
# This task used to prove a hand-copied FORK of the RTL (<module>_formal.sv), kept
# because yosys's own SystemVerilog frontend could not read the real module.
# sv2v can, so the fork is gone and the proof is about the shipped design.
# Regenerate the flat file whenever the RTL changes. (2026-09-11)

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := axi_split_combi_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/amba/filelists/axi_split_combi.f
FLAT_SV2V_FLAGS := --define=FORMAL
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: axi_split_combi_flat.v
	sby -f axi_split_combi.sby prove

cover: axi_split_combi_flat.v
	sby -f axi_split_combi.sby cover

clean:
	rm -rf axi_split_combi_prove axi_split_combi_cover
