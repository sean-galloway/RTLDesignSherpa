# SPDX-License-Identifier: MIT
# Formal verification Makefile for cdc_4_phase_handshake
# Workflow: sv2v flattens the REAL RTL -> sby reads plain Verilog (plain prep).
#
# This task used to prove a hand-copied FORK of the RTL (<module>_formal.sv), kept
# because yosys's own SystemVerilog frontend could not read the real module.
# sv2v can, so the fork is gone and the proof is about the shipped design.
# Regenerate the flat file whenever the RTL changes. (2026-09-11)

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v
INC  := -I$(REPO_ROOT)/rtl/amba/includes
PKGS := 
SRCS := $(REPO_ROOT)/rtl/cdc/cdc_4_phase_handshake.sv
TMPDIR := /tmp/formal_cdc_4_phase_handshake

.PHONY: prove cover all clean

all: prove cover

prove: cdc_4_phase_handshake_flat.v
	sby -f cdc_4_phase_handshake.sby prove

cover: cdc_4_phase_handshake_flat.v
	sby -f cdc_4_phase_handshake.sby cover

cdc_4_phase_handshake_flat.v: $(PKGS) $(SRCS)
	@mkdir -p $(TMPDIR)
	@for f in $(SRCS); do cp $$f $(TMPDIR)/; done
	$(SV2V) --define=FORMAL $(INC) $(PKGS) $(addprefix $(TMPDIR)/,$(notdir $(SRCS))) > $@
	@rm -rf $(TMPDIR)

clean:
	rm -rf cdc_4_phase_handshake_prove cdc_4_phase_handshake_cover
