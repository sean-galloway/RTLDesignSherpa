# SPDX-License-Identifier: MIT
# Formal verification Makefile for scoria_global_timers
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
SCORIA    := $(REPO_ROOT)/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(SCORIA)/rtl/includes
PKGS := $(SCORIA)/rtl/includes/scoria_pkg.sv
DUT  := $(SCORIA)/rtl/fub/scoria_global_timers.sv

.PHONY: prove cover all clean

all: prove cover

prove: global_timers_flat.v
	sby -f scoria_global_timers.sby prove

cover: global_timers_flat.v
	sby -f scoria_global_timers.sby cover

global_timers_flat.v: $(DUT) $(PKGS)
	$(SV2V) $(INC) $(PKGS) $(DUT) > $@

clean:
	rm -rf *_flat.v global_timers_prove global_timers_cover
