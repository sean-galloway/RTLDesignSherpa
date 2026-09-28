# SPDX-License-Identifier: MIT
# Formal verification Makefile for refresh_ctrl (pumice)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
PUMICE    := $(REPO_ROOT)/projects/components/memory-controllers/pumice-ddr2-lpddr2

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(PUMICE)/rtl/includes
PKGS := $(PUMICE)/rtl/includes/pumice_pkg.sv
DUT  := $(PUMICE)/rtl/fub/refresh_ctrl.sv

.PHONY: prove cover all clean

all: prove cover

prove: refresh_ctrl_flat.v
	sby -f refresh_ctrl.sby prove

cover: refresh_ctrl_flat.v
	sby -f refresh_ctrl.sby cover

refresh_ctrl_flat.v: $(DUT) $(PKGS)
	$(SV2V) $(INC) $(PKGS) $(DUT) > $@

clean:
	rm -rf *_flat.v refresh_ctrl_prove refresh_ctrl_cover
