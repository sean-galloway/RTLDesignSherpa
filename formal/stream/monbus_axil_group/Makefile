# SPDX-License-Identifier: MIT
# Formal verification Makefile for monbus_axil_group
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(REPO_ROOT)/projects/components/stream/rtl/includes

# Package files (order matters: dependencies first)
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv

# RTL dependencies
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv \
        $(REPO_ROOT)/rtl/amba/axil4/axil4_slave_rd.sv \
        $(REPO_ROOT)/rtl/amba/axil4/axil4_master_wr.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/stream/rtl/macro/monbus_axil_group.sv

.PHONY: prove cover clean

prove: monbus_axil_group_flat.v
	sby -f monbus_axil_group.sby prove

cover: monbus_axil_group_flat.v
	sby -f monbus_axil_group.sby cover

monbus_axil_group_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
