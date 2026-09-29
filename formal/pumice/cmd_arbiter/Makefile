# SPDX-License-Identifier: MIT
# Formal verification Makefile for pumice_cmd_arbiter COMPOSED with global_timers.
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# Both modules are flattened together because the proof is about the LOOP
# between them -- see formal_cmd_arbiter.sv.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
PUMICE    := $(REPO_ROOT)/projects/components/memory-controllers/pumice-ddr2-lpddr2

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(PUMICE)/rtl/includes
PKGS := $(PUMICE)/rtl/includes/pumice_pkg.sv
DUT  := $(PUMICE)/rtl/fub/global_timers.sv $(PUMICE)/rtl/fub/pumice_cmd_arbiter.sv

.PHONY: prove issue019 cover all clean
# `all` deliberately excludes issue019: those assertions FAIL by design -- they
# are the reproduction for pumice BUG-021, not a regression signal.
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
