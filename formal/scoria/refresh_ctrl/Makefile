# SPDX-License-Identifier: MIT
# Formal verification Makefile for scoria_refresh_ctrl
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
SCORIA    := $(REPO_ROOT)/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3
# scoria_pkg imports and re-exports mc_common_pkg (the family package in common-ip)
MC        := $(REPO_ROOT)/projects/components/mem-ctrl-ip/common-ip

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(MC)/rtl/includes -I$(SCORIA)/rtl/includes
PKGS := $(MC)/rtl/includes/mc_common_pkg.sv $(SCORIA)/rtl/includes/scoria_pkg.sv
DUT  := $(SCORIA)/rtl/fub/scoria_refresh_ctrl.sv

.PHONY: prove cover all clean

all: prove cover

prove: refresh_ctrl_flat.v
	sby -f scoria_refresh_ctrl.sby prove

cover: refresh_ctrl_flat.v
	sby -f scoria_refresh_ctrl.sby cover

refresh_ctrl_flat.v: $(DUT) $(PKGS)
	$(SV2V) $(INC) $(PKGS) $(DUT) > $@

clean:
	rm -rf *_flat.v refresh_ctrl_prove refresh_ctrl_cover
