# SPDX-License-Identifier: MIT
# Formal verification Makefile for wb4_master_cg
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
# (same shape as formal/amba/wb4_master/Makefile).

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

PKGS := $(REPO_ROOT)/rtl/amba/wb4/wb4_pkg.sv
# icg.sv deliberately absent: the harness supplies a clock-enable model of the cell.
DEPS := $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv $(REPO_ROOT)/rtl/common/clock_gate_ctrl.sv $(REPO_ROOT)/rtl/amba/shared/amba_clock_gate_ctrl.sv $(REPO_ROOT)/rtl/amba/wb4/wb4_master.sv
DUT  := $(REPO_ROOT)/rtl/amba/wb4/wb4_master_cg.sv

.PHONY: prove cover all clean

all: prove cover

prove: wb4_master_cg_flat.v
	sby -f wb4_master_cg.sby prove

cover: wb4_master_cg_flat.v
	sby -f wb4_master_cg.sby cover

wb4_master_cg_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(DEPS) $(DUT) > $@
	@echo "asserts in flat: $$(grep -c 'assert' $@)"

clean:
	rm -rf *_flat.v *_prove *_cover
