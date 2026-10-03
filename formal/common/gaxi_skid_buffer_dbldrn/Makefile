# SPDX-License-Identifier: MIT
# Formal verification Makefile for gaxi_skid_buffer_dbldrn
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
SRCS := $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer_dbldrn.sv
TMPDIR := /tmp/formal_gaxi_skid_buffer_dbldrn

.PHONY: prove cover all clean

all: prove cover

prove: gaxi_skid_buffer_dbldrn_flat.v
	sby -f gaxi_skid_buffer_dbldrn.sby prove

cover: gaxi_skid_buffer_dbldrn_flat.v
	sby -f gaxi_skid_buffer_dbldrn.sby cover

gaxi_skid_buffer_dbldrn_flat.v: $(PKGS) $(SRCS)
	@mkdir -p $(TMPDIR)
	@for f in $(SRCS); do cp $$f $(TMPDIR)/; done
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(addprefix $(TMPDIR)/,$(notdir $(SRCS))) > $@
	@rm -rf $(TMPDIR)

clean:
	rm -rf gaxi_skid_buffer_dbldrn_prove gaxi_skid_buffer_dbldrn_cover

# tooling TASK-026: regenerate-and-diff self-detection for the committed flat.
# House pattern from formal/common/counter_freq_invariant; consumed by
# bin/formal_status.py --check-flats (mechanism a) and the pre-commit gate.
# Comparison squeezes whitespace, matching the token normalization the
# checker uses (committed flats may be post-formatter).
.PHONY: check-flat .check_flat_tmp
check-flat: .check_flat_tmp
	@if [ "$$(tr -s '[:space:]' ' ' < .check_flat_tmp)" = "$$(tr -s '[:space:]' ' ' < gaxi_skid_buffer_dbldrn_flat.v)" ]; then \
		rm -f .check_flat_tmp; \
		echo "flat file is current"; \
	else \
		rm -f .check_flat_tmp; \
		echo "STALE: gaxi_skid_buffer_dbldrn_flat.v does not match the RTL."; \
		echo "Regenerate with: make gaxi_skid_buffer_dbldrn_flat.v"; \
		exit 1; \
	fi

.check_flat_tmp: $(PKGS) $(SRCS)
	@mkdir -p $(TMPDIR)
	@for f in $(SRCS); do cp $$f $(TMPDIR)/; done
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(addprefix $(TMPDIR)/,$(notdir $(SRCS))) > $@
	@rm -rf $(TMPDIR)

clean:
	rm -rf gaxi_skid_buffer_dbldrn_prove gaxi_skid_buffer_dbldrn_cover
