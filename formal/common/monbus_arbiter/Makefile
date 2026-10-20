# SPDX-License-Identifier: MIT
# Formal verification Makefile for monbus_arbiter
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
FLAT            := monbus_arbiter_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/amba/filelists/monbus_arbiter.f
FLAT_SV2V_FLAGS := --define=FORMAL
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: monbus_arbiter_flat.v
	sby -f monbus_arbiter.sby prove

cover: monbus_arbiter_flat.v
	sby -f monbus_arbiter.sby cover

clean:
	rm -rf monbus_arbiter_prove monbus_arbiter_cover
