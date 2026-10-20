# SPDX-License-Identifier: MIT
# Formal verification Makefile for cdc_4_phase_handshake
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
FLAT            := cdc_4_phase_handshake_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/cdc/filelists/cdc_4_phase_handshake.f
FLAT_SV2V_FLAGS := --define=FORMAL
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover prove_timeout cover_timeout all clean

all: prove cover prove_timeout cover_timeout

prove: cdc_4_phase_handshake_flat.v
	sby -f cdc_4_phase_handshake.sby prove

cover: cdc_4_phase_handshake_flat.v
	sby -f cdc_4_phase_handshake.sby cover

# The parameterised configurations. Each sby task needs its OWN make target:
# bin/formal_status.py drives tasks through this Makefile, so a task that is
# in the .sby but not here is INVISIBLE to the measured table -- it reported
# NORESULT and the CDC-002 finding would not have shown up at all. (2026-09-16)
prove_timeout: cdc_4_phase_handshake_flat.v
	sby -f cdc_4_phase_handshake.sby prove_timeout

cover_timeout: cdc_4_phase_handshake_flat.v
	sby -f cdc_4_phase_handshake.sby cover_timeout

clean:
	rm -rf cdc_4_phase_handshake_prove cdc_4_phase_handshake_cover
