# SPDX-License-Identifier: MIT
# Formal verification Makefile for math_fp8_e5m2_clamp
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
SRCS := $(REPO_ROOT)/rtl/math/math_fp8_e5m2_clamp.sv
TMPDIR := /tmp/formal_math_fp8_e5m2_clamp

.PHONY: prove cover all clean

all: prove cover

prove: math_fp8_e5m2_clamp_flat.v
	sby -f math_fp8_e5m2_clamp.sby prove

cover: math_fp8_e5m2_clamp_flat.v
	sby -f math_fp8_e5m2_clamp.sby cover

math_fp8_e5m2_clamp_flat.v: $(PKGS) $(SRCS)
	@mkdir -p $(TMPDIR)
	@for f in $(SRCS); do cp $$f $(TMPDIR)/; done
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(addprefix $(TMPDIR)/,$(notdir $(SRCS))) > $@
	@rm -rf $(TMPDIR)

clean:
	rm -rf math_fp8_e5m2_clamp_prove math_fp8_e5m2_clamp_cover

# tooling TASK-026: regenerate-and-diff self-detection for the committed flat.
# House pattern from formal/common/counter_freq_invariant; consumed by
# bin/formal_status.py --check-flats (mechanism a) and the pre-commit gate.
# Comparison squeezes whitespace, matching the token normalization the
# checker uses (committed flats may be post-formatter).
.PHONY: check-flat .check_flat_tmp
check-flat: .check_flat_tmp
	@if [ "$$(tr -s '[:space:]' ' ' < .check_flat_tmp)" = "$$(tr -s '[:space:]' ' ' < math_fp8_e5m2_clamp_flat.v)" ]; then \
		rm -f .check_flat_tmp; \
		echo "flat file is current"; \
	else \
		rm -f .check_flat_tmp; \
		echo "STALE: math_fp8_e5m2_clamp_flat.v does not match the RTL."; \
		echo "Regenerate with: make math_fp8_e5m2_clamp_flat.v"; \
		exit 1; \
	fi

.check_flat_tmp: $(PKGS) $(SRCS)
	@mkdir -p $(TMPDIR)
	@for f in $(SRCS); do cp $$f $(TMPDIR)/; done
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(addprefix $(TMPDIR)/,$(notdir $(SRCS))) > $@
	@rm -rf $(TMPDIR)