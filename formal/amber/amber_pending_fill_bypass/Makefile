# SPDX-License-Identifier: MIT
# Formal verification Makefile for amber_pending_fill_bypass
# Workflow: sv2v flattens the REAL RTL -> sby reads plain Verilog (plain prep).
#
# Geometry: the tiny formal configuration SETS=16 / LINE_BYTES=64 / BUS_WIDTH=64
# (amber_pkg defaults are 128/64/64; the wrapper pins the formal geometry the
# same way the amber DV grid does).
# Regenerate the flat file whenever the RTL changes.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
INC  := -I$(REPO_ROOT)/rtl/amba/includes
PKGS := $(REPO_ROOT)/projects/components/cache-ip/amber-mesi-l1/rtl/includes/amber_pkg.sv
SRCS := $(REPO_ROOT)/projects/components/cache-ip/amber-mesi-l1/rtl/fub/amber_pending_fill_bypass.sv
TMPDIR := /tmp/formal_amber_pending_fill_bypass

.PHONY: prove cover all clean

all: prove cover

prove: amber_pending_fill_bypass_flat.v
	sby -f amber_pending_fill_bypass.sby prove

cover: amber_pending_fill_bypass_flat.v
	sby -f amber_pending_fill_bypass.sby cover

amber_pending_fill_bypass_flat.v: $(PKGS) $(SRCS)
	@mkdir -p $(TMPDIR)
	@for f in $(SRCS); do cp $$f $(TMPDIR)/; done
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(addprefix $(TMPDIR)/,$(notdir $(SRCS))) > $@
	@rm -rf $(TMPDIR)

clean:
	rm -rf amber_pending_fill_bypass_prove amber_pending_fill_bypass_cover

# tooling TASK-026: regenerate-and-diff self-detection for the committed flat.
# House pattern from formal/common/counter_freq_invariant; consumed by
# bin/formal_status.py --check-flats (mechanism a) and the pre-commit gate.
# Comparison squeezes whitespace, matching the token normalization the
# checker uses (committed flats may be post-formatter).
.PHONY: check-flat .check_flat_tmp
check-flat: .check_flat_tmp
	@if [ "$$(tr -s '[:space:]' ' ' < .check_flat_tmp)" = "$$(tr -s '[:space:]' ' ' < amber_pending_fill_bypass_flat.v)" ]; then \
		rm -f .check_flat_tmp; \
		echo "flat file is current"; \
	else \
		rm -f .check_flat_tmp; \
		echo "STALE: amber_pending_fill_bypass_flat.v does not match the RTL."; \
		echo "Regenerate with: make amber_pending_fill_bypass_flat.v"; \
		exit 1; \
	fi

.check_flat_tmp: $(PKGS) $(SRCS)
	@mkdir -p $(TMPDIR)
	@for f in $(SRCS); do cp $$f $(TMPDIR)/; done
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(addprefix $(TMPDIR)/,$(notdir $(SRCS))) > $@
	@rm -rf $(TMPDIR)
