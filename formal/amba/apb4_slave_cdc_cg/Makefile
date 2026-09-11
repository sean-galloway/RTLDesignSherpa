# SPDX-License-Identifier: MIT
# Formal verification Makefile for apb4_slave_cdc_cg
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
#
# This task used to read the RTL directly. Yosys's own SystemVerilog frontend
# cannot parse the constructs this module uses, so the proof never ran at all;
# sv2v handles them, which is the same route apb4_monitor and the wb4 family
# take. Regenerate the flat file whenever the RTL changes -- a stale flat is a
# proof about code that no longer exists.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

# icg.sv deliberately ABSENT: the harness supplies a clock-enable model
# of the cell, because a derived clock is not provable in this flow.
DEPS := $(REPO_ROOT)/rtl/common/clock_gate_ctrl.sv \
        $(REPO_ROOT)/rtl/amba/shared/amba_clock_gate_ctrl.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv \
        $(REPO_ROOT)/rtl/amba/apb4/apb4_slave.sv \
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
        $(REPO_ROOT)/rtl/cdc/gaxi_fifo_async.sv
DUT  := $(REPO_ROOT)/rtl/amba/apb4/apb4_slave_cdc_cg.sv

.PHONY: prove cover all clean

all: prove cover

prove: apb4_slave_cdc_cg_flat.v
	sby -f apb4_slave_cdc_cg.sby prove

cover: apb4_slave_cdc_cg_flat.v
	sby -f apb4_slave_cdc_cg.sby cover

apb4_slave_cdc_cg_flat.v: $(DUT) $(DEPS)
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(DEPS) $(DUT) > $@

clean:
	rm -rf apb4_slave_cdc_cg_flat.v apb4_slave_cdc_cg_prove apb4_slave_cdc_cg_cover
