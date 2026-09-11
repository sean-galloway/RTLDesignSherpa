# SPDX-License-Identifier: MIT
# Formal verification Makefile for wb4_slave_cdc_cg
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
#
# This block had NO proof until 2026-09-11, while every APB family proved all
# three of <x>_slave_cdc, <x>_slave_cg and <x>_slave_cdc_cg. The gap was in no
# tracker, so nothing surfaced it.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

INC  := -I$(REPO_ROOT)/rtl/amba/includes
PKGS := $(REPO_ROOT)/rtl/amba/wb4/wb4_pkg.sv

# icg.sv is deliberately ABSENT: the harness supplies a clock-enable model of
# the cell, because a derived clock is not provable in the single-clock flow.
DEPS := $(REPO_ROOT)/rtl/common/clock_gate_ctrl.sv \
        $(REPO_ROOT)/rtl/amba/shared/amba_clock_gate_ctrl.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv \
        $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/cdc/counter_johnson.sv \
        $(REPO_ROOT)/rtl/cdc/counter_bingray.sv \
        $(REPO_ROOT)/rtl/cdc/glitch_free_n_dff_arn.sv \
        $(REPO_ROOT)/rtl/common/find_last_set.sv \
        $(REPO_ROOT)/rtl/common/find_first_set.sv \
        $(REPO_ROOT)/rtl/common/leading_one_trailing_one.sv \
        $(REPO_ROOT)/rtl/cdc/johnson2bin.sv \
        $(REPO_ROOT)/rtl/cdc/gray2bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/cdc/gaxi_fifo_async.sv \
        $(REPO_ROOT)/rtl/amba/wb4/wb4_slave.sv \
        $(REPO_ROOT)/rtl/amba/wb4/wb4_slave_cdc.sv
DUT  := $(REPO_ROOT)/rtl/amba/wb4/wb4_slave_cdc_cg.sv

.PHONY: prove cover all clean

all: prove cover

prove: wb4_slave_cdc_cg_flat.v
	sby -f wb4_slave_cdc_cg.sby prove

cover: wb4_slave_cdc_cg_flat.v
	sby -f wb4_slave_cdc_cg.sby cover

wb4_slave_cdc_cg_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf wb4_slave_cdc_cg_flat.v wb4_slave_cdc_cg_prove wb4_slave_cdc_cg_cover
