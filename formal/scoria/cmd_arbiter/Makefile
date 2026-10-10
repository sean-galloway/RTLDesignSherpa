# SPDX-License-Identifier: MIT
# Formal verification for scoria_cmd_arbiter COMPOSED with scoria_global_timers.
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# Both modules are flattened together because the proof is about the LOOP
# between them -- see formal_scoria_cmd_arbiter.sv.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
SCORIA    := $(REPO_ROOT)/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(SCORIA)/rtl/includes
PKGS := $(SCORIA)/rtl/includes/scoria_pkg.sv
DUT  := $(SCORIA)/rtl/fub/scoria_global_timers.sv $(SCORIA)/rtl/fub/scoria_cmd_arbiter.sv

.PHONY: prove nofix cover all clean
# `all` deliberately excludes nofix: that task re-proves the PRE-FIX gate and
# is expected to FAIL. It is what makes the passing proof mean something, and
# it is not a regression signal.
all: prove cover

prove: arb_flat.v
	sby -f scoria_cmd_arbiter.sby prove

# The BUG-001 properties disarmed. Only useful paired with a reverted gate --
# on the fixed RTL this proves strictly less than `prove`.
nofix: arb_flat.v
	sby -f scoria_cmd_arbiter.sby nofix

cover: arb_flat.v
	sby -f scoria_cmd_arbiter.sby cover

arb_flat.v: $(DUT) $(PKGS)
	$(SV2V) $(INC) $(PKGS) $(DUT) > $@

clean:
	rm -rf *_flat.v arb_flat.v scoria_cmd_arbiter_prove \
	       scoria_cmd_arbiter_nofix scoria_cmd_arbiter_cover

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