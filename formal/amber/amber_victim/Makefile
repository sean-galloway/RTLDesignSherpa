# SPDX-License-Identifier: MIT
# Formal verification Makefile for amber_victim
# Workflow: sv2v flattens the REAL RTL -> sby reads plain Verilog (plain prep).
#
# Geometry: the tiny formal configuration SETS=16 / LINE_BYTES=64 / BUS_WIDTH=64
# (the register is geometry-parameterized only by the line width; SETS is a
# bound contract).
# Regenerate the flat file whenever the RTL changes.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
INC  := -I$(REPO_ROOT)/rtl/amba/includes
PKGS := $(REPO_ROOT)/projects/components/cache-ip/amber-mesi-l1/rtl/includes/amber_pkg.sv
SRCS := $(REPO_ROOT)/projects/components/cache-ip/amber-mesi-l1/rtl/fub/amber_victim.sv
TMPDIR := /tmp/formal_amber_victim

.PHONY: prove cover all clean

all: prove cover

prove: amber_victim_flat.v
	sby -f amber_victim.sby prove

cover: amber_victim_flat.v
	sby -f amber_victim.sby cover

amber_victim_flat.v: $(PKGS) $(SRCS)
	@mkdir -p $(TMPDIR)
	@for f in $(SRCS); do cp $$f $(TMPDIR)/; done
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(addprefix $(TMPDIR)/,$(notdir $(SRCS))) > $@
	@rm -rf $(TMPDIR)

clean:
	rm -rf amber_victim_prove amber_victim_cover

# tooling TASK-026: regenerate-and-diff self-detection for the committed flat.
# House pattern from formal/common/counter_freq_invariant; consumed by
# bin/formal_status.py --check-flats (mechanism a) and the pre-commit gate.
# Comparison squeezes whitespace, matching the token normalization the
# checker uses (committed flats may be post-formatter).
.PHONY: check-flat .check_flat_tmp
check-flat: .check_flat_tmp
	@if [ "$$(tr -s '[:space:]' ' ' < .check_flat_tmp)" = "$$(tr -s '[:space:]' ' ' < amber_victim_flat.v)" ]; then \
		rm -f .check_flat_tmp; \
		echo "flat file is current"; \
	else \
		rm -f .check_flat_tmp; \
		echo "STALE: amber_victim_flat.v does not match the RTL."; \
		echo "Regenerate with: make amber_victim_flat.v"; \
		exit 1; \
	fi

.check_flat_tmp: $(PKGS) $(SRCS)
	@mkdir -p $(TMPDIR)
	@for f in $(SRCS); do cp $$f $(TMPDIR)/; done
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(addprefix $(TMPDIR)/,$(notdir $(SRCS))) > $@
	@rm -rf $(TMPDIR)
