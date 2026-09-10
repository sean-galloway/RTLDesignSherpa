# SPDX-License-Identifier: MIT
# Formal verification Makefile for wb4_slave_cdc
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
# (same shape as formal/amba/wb4_master/Makefile).

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

PKGS := $(REPO_ROOT)/rtl/amba/wb4/wb4_pkg.sv
DEPS := $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv $(REPO_ROOT)/rtl/common/counter_bin.sv $(REPO_ROOT)/rtl/cdc/glitch_free_n_dff_arn.sv $(REPO_ROOT)/rtl/common/find_first_set.sv $(REPO_ROOT)/rtl/common/find_last_set.sv $(REPO_ROOT)/rtl/common/leading_one_trailing_one.sv $(REPO_ROOT)/rtl/common/fifo_control.sv $(REPO_ROOT)/rtl/cdc/gray2bin.sv $(REPO_ROOT)/rtl/cdc/counter_bingray.sv $(REPO_ROOT)/rtl/cdc/counter_johnson.sv $(REPO_ROOT)/rtl/cdc/johnson2bin.sv $(REPO_ROOT)/rtl/cdc/gaxi_fifo_async.sv $(REPO_ROOT)/rtl/amba/wb4/wb4_slave.sv
DUT  := $(REPO_ROOT)/rtl/amba/wb4/wb4_slave_cdc.sv

.PHONY: prove cover all clean

all: prove cover

prove: wb4_slave_cdc_flat.v
	sby -f wb4_slave_cdc.sby prove

cover: wb4_slave_cdc_flat.v
	sby -f wb4_slave_cdc.sby cover

wb4_slave_cdc_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(DEPS) $(DUT) > $@
	@echo "asserts in flat: $$(grep -c 'assert' $@)"

clean:
	rm -rf *_flat.v *_prove *_cover
