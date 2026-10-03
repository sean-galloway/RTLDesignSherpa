# SPDX-License-Identifier: MIT
# Formal verification Makefile for pumice_cmd_arbiter COMPOSED with global_timers.
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# Both modules are flattened together because the proof is about the LOOP
# between them -- see formal_cmd_arbiter.sv.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
PUMICE    := $(REPO_ROOT)/projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(PUMICE)/rtl/includes
PKGS := $(PUMICE)/rtl/includes/pumice_pkg.sv
DUT  := $(PUMICE)/rtl/fub/global_timers.sv $(PUMICE)/rtl/fub/pumice_cmd_arbiter.sv

.PHONY: prove issue019 cover all clean
# `issue019` was the held-red reproduction for pumice BUG-021 (the tRRD/tFAW
# fire-stage gap). The gap is fixed -- w_out_safe re-checks the rank-global
# windows live at the fire -- and the .sby now arms the ISSUE019 assertions for
# every task, so `prove` (and the formal/pumice area dispatch) guards the fix
# directly. `make issue019` stays as a named entry point to the same armed
# task.
all: prove cover
prove: arb_flat.v
	sby -f cmd_arbiter.sby prove
issue019: arb_flat.v
	sby -f cmd_arbiter.sby issue019

cover: arb_flat.v
	sby -f cmd_arbiter.sby cover
arb_flat.v: $(DUT) $(PKGS)
	$(SV2V) $(INC) $(PKGS) $(DUT) > $@
clean:
	rm -rf *_flat.v arb_flat.v cmd_arbiter_prove cmd_arbiter_issue019 cmd_arbiter_cover

# tooling TASK-026: regenerate-and-diff self-detection for the committed flat.
# House pattern from formal/common/counter_freq_invariant; consumed by
# bin/formal_status.py --check-flats (mechanism a) and the pre-commit gate.
# Comparison squeezes whitespace, matching the token normalization the
# checker uses (committed flats may be post-formatter).
.PHONY: check-flat .check_flat_tmp
check-flat: .check_flat_tmp
	@if [ "$$(tr -s '[:space:]' ' ' < .check_flat_tmp)" = "$$(tr -s '[:space:]' ' ' < arb_flat.v)" ]; then \
		rm -f .check_flat_tmp; \
		echo "flat file is current"; \
	else \
		rm -f .check_flat_tmp; \
		echo "STALE: arb_flat.v does not match the RTL."; \
		echo "Regenerate with: make arb_flat.v"; \
		exit 1; \
	fi

.check_flat_tmp: $(DUT) $(PKGS)
	$(SV2V) $(INC) $(PKGS) $(DUT) > $@
clean:
	rm -rf *_flat.v $@ cmd_arbiter_prove cmd_arbiter_issue019 cmd_arbiter_cover
