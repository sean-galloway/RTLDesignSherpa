# SPDX-License-Identifier: MIT
# Formal verification Makefile for amber_control
# Workflow: sv2v flattens the REAL RTL -> sby reads plain Verilog (plain prep).
#
# Closure: amber_pkg + amber_pending_fill_bypass + amber_victim (the two leaf
# sub-blocks control instantiates) + amber_control. The tag/data/repl arrays
# stay outside: the wrapper models the tag store abstractly and frees the
# rest (see formal_amber_control.sv).
# Geometry: the tiny formal configuration SETS=16 / WAYS=2 / 64B / 64b.
# Regenerate the flat file whenever the RTL changes.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
INC  := -I$(REPO_ROOT)/rtl/amba/includes
PKGS := $(REPO_ROOT)/projects/components/cache-ip/amber-mesi-l1/rtl/includes/amber_pkg.sv
SRCS := $(REPO_ROOT)/projects/components/cache-ip/amber-mesi-l1/rtl/fub/amber_pending_fill_bypass.sv \
        $(REPO_ROOT)/projects/components/cache-ip/amber-mesi-l1/rtl/fub/amber_victim.sv \
        $(REPO_ROOT)/projects/components/cache-ip/amber-mesi-l1/rtl/fub/amber_control.sv
TMPDIR := /tmp/formal_amber_control

.PHONY: prove prove-live cover all clean

all: prove prove-live cover

prove: amber_control_flat.v
	sby -f amber_control.sby prove

# bounded-liveness (no deadlock/livelock) -- model-free wrapper, BMC
prove-live: amber_control_flat.v
	sby -f amber_control_live.sby prove

cover: amber_control_flat.v
	sby -f amber_control.sby cover

amber_control_flat.v: $(PKGS) $(SRCS)
	@mkdir -p $(TMPDIR)
	@for f in $(SRCS); do cp $$f $(TMPDIR)/; done
	# sv2v flattens the REAL RTL; specialize_params then pins the tiny formal
	# geometry AND deletes the parameter declarations, so the DUT becomes a
	# truly parameterless module: yosys's expose command (the
	# internal-observability mechanism in the .sby script) applies cleanly,
	# and the wrapper can observe DUT internals. bind is NOT usable in this
	# yosys build -- it silently never fires; see the Task 13 report.
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(addprefix $(TMPDIR)/,$(notdir $(SRCS))) | python3 ../specialize_params.py - $@ \
	    --param ADDR_WIDTH=32 --param SETS=16 --param WAYS=2 \
	    --param LINE_BYTES=64 --param BUS_WIDTH=64 \
	    --module amber_control
	@rm -rf $(TMPDIR)

clean:
	rm -rf amber_control_prove amber_control_cover amber_control_live_prove

# tooling TASK-026: regenerate-and-diff self-detection for the committed flat.
# House pattern from formal/common/counter_freq_invariant; consumed by
# bin/formal_status.py --check-flats (mechanism a) and the pre-commit gate.
# Comparison squeezes whitespace, matching the token normalization the
# checker uses (committed flats may be post-formatter).
.PHONY: check-flat .check_flat_tmp
check-flat: .check_flat_tmp
	@if [ "$$(tr -s '[:space:]' ' ' < .check_flat_tmp)" = "$$(tr -s '[:space:]' ' ' < amber_control_flat.v)" ]; then \
		rm -f .check_flat_tmp; \
		echo "flat file is current"; \
	else \
		rm -f .check_flat_tmp; \
		echo "STALE: amber_control_flat.v does not match the RTL."; \
		echo "Regenerate with: make amber_control_flat.v"; \
		exit 1; \
	fi

.check_flat_tmp: $(PKGS) $(SRCS)
	@mkdir -p $(TMPDIR)
	@for f in $(SRCS); do cp $$f $(TMPDIR)/; done
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(addprefix $(TMPDIR)/,$(notdir $(SRCS))) | python3 ../specialize_params.py - $@ \
	    --param ADDR_WIDTH=32 --param SETS=16 --param WAYS=2 \
	    --param LINE_BYTES=64 --param BUS_WIDTH=64 \
	    --module amber_control
	@rm -rf $(TMPDIR)
