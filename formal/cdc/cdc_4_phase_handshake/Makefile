# SPDX-License-Identifier: MIT
# Formal verification Makefile for cdc_4_phase_handshake
# Workflow: sv2v flattens the REAL RTL -> sby reads plain Verilog (plain prep).
#
# This task used to prove a hand-copied FORK of the RTL (<module>_formal.sv), kept
# because yosys's own SystemVerilog frontend could not read the real module.
# sv2v can, so the fork is gone and the proof is about the shipped design.
# Regenerate the flat file whenever the RTL changes. (2026-09-11)

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
INC  := -I$(REPO_ROOT)/rtl/amba/includes
PKGS := 
SRCS := $(REPO_ROOT)/rtl/cdc/cdc_4_phase_handshake.sv
TMPDIR := /tmp/formal_cdc_4_phase_handshake

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


cdc_4_phase_handshake_flat.v: $(PKGS) $(SRCS)
	@mkdir -p $(TMPDIR)
	@for f in $(SRCS); do cp $$f $(TMPDIR)/; done
	$(SV2V) --define=FORMAL $(INC) $(PKGS) $(addprefix $(TMPDIR)/,$(notdir $(SRCS))) > $@
	@rm -rf $(TMPDIR)

clean:
	rm -rf cdc_4_phase_handshake_prove cdc_4_phase_handshake_cover

# tooling TASK-026: regenerate-and-diff self-detection for the committed flat.
# House pattern from formal/common/counter_freq_invariant; consumed by
# bin/formal_status.py --check-flats (mechanism a) and the pre-commit gate.
# Comparison squeezes whitespace, matching the token normalization the
# checker uses (committed flats may be post-formatter).
.PHONY: check-flat .check_flat_tmp
check-flat: .check_flat_tmp
	@if [ "$$(tr -s '[:space:]' ' ' < .check_flat_tmp)" = "$$(tr -s '[:space:]' ' ' < cdc_4_phase_handshake_flat.v)" ]; then \
		rm -f .check_flat_tmp; \
		echo "flat file is current"; \
	else \
		rm -f .check_flat_tmp; \
		echo "STALE: cdc_4_phase_handshake_flat.v does not match the RTL."; \
		echo "Regenerate with: make cdc_4_phase_handshake_flat.v"; \
		exit 1; \
	fi

.check_flat_tmp: $(PKGS) $(SRCS)
	@mkdir -p $(TMPDIR)
	@for f in $(SRCS); do cp $$f $(TMPDIR)/; done
	$(SV2V) --define=FORMAL $(INC) $(PKGS) $(addprefix $(TMPDIR)/,$(notdir $(SRCS))) > $@
	@rm -rf $(TMPDIR)

clean:
	rm -rf cdc_4_phase_handshake_prove cdc_4_phase_handshake_cover
