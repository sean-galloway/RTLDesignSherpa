# SPDX-License-Identifier: MIT
# Formal verification Makefile for scoria_bank_timer
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
#
# The flatten is not optional here: yosys's Verilog frontend cannot parse
# scoria_pkg.sv (a multi-line `return` in a package function, scoria_pkg.sv:131),
# so reading the .sv directly fails before any proof runs.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
SCORIA    := $(REPO_ROOT)/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(SCORIA)/rtl/includes
PKGS := $(SCORIA)/rtl/includes/scoria_pkg.sv
DUT  := $(SCORIA)/rtl/fub/scoria_bank_timer.sv

.PHONY: prove cover all clean

all: prove cover

prove: bank_timer_flat.v
	sby -f scoria_bank_timer.sby prove

cover: bank_timer_flat.v
	sby -f scoria_bank_timer.sby cover

bank_timer_flat.v: $(DUT) $(PKGS)
	$(SV2V) $(INC) $(PKGS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
