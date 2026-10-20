# SPDX-License-Identifier: MIT
# Formal verification Makefile for gaxi_skid_buffer_dbldrn
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
FLAT            := gaxi_skid_buffer_dbldrn_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/amba/filelists/gaxi_skid_buffer_dbldrn.f
# --define=FORMAL keeps the in-RTL formal blocks; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (vault/handbook/dv/formal.md).
FLAT_SV2V_FLAGS := --define=FORMAL --exclude=Assert
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: gaxi_skid_buffer_dbldrn_flat.v
	sby -f gaxi_skid_buffer_dbldrn.sby prove

cover: gaxi_skid_buffer_dbldrn_flat.v
	sby -f gaxi_skid_buffer_dbldrn.sby cover

clean:
	rm -rf gaxi_skid_buffer_dbldrn_prove gaxi_skid_buffer_dbldrn_cover
