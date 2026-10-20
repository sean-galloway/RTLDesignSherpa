# SPDX-License-Identifier: MIT
# Formal verification Makefile for sync_pulse
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
FLAT            := sync_pulse_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/cdc/filelists/sync_pulse.f
FLAT_SV2V_FLAGS := --define=FORMAL
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: sync_pulse_flat.v
	sby -f sync_pulse.sby prove

cover: sync_pulse_flat.v
	sby -f sync_pulse.sby cover

clean:
	rm -rf sync_pulse_prove sync_pulse_cover
