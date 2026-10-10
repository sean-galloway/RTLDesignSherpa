# SPDX-License-Identifier: MIT
# Formal verification Makefile for bank_timer (pumice)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
#
# The flatten is not optional here: yosys's Verilog frontend cannot parse
# pumice_pkg.sv (a multi-line `return` in a package function, pumice_pkg.sv:131),
# so reading the .sv directly fails before any proof runs.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
PUMICE    := $(REPO_ROOT)/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/pumice-ddr2-lpddr2

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(PUMICE)/rtl/includes
PKGS := $(PUMICE)/rtl/includes/pumice_pkg.sv
DUT  := $(PUMICE)/rtl/fub/bank_timer.sv

.PHONY: prove cover all clean

all: prove cover

prove: bank_timer_flat.v
	sby -f bank_timer.sby prove

cover: bank_timer_flat.v
	sby -f bank_timer.sby cover

bank_timer_flat.v: $(DUT) $(PKGS)
	$(SV2V) $(INC) $(PKGS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
