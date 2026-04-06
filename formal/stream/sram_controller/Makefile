# SPDX-License-Identifier: MIT
# Formal verification Makefile for sram_controller
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(REPO_ROOT)/projects/components/stream/rtl/includes

# Package files (order matters: dependencies first)
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/includes/stream_pkg.sv

# RTL dependencies (all of sram_controller_unit's deps plus the unit itself)
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/stream_alloc_ctrl.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/stream_drain_ctrl.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/stream_latency_bridge.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/sram_controller_unit.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/stream/rtl/fub/sram_controller.sv

.PHONY: prove cover clean

prove: sram_controller_flat.v
	sby -f sram_controller.sby prove

cover: sram_controller_flat.v
	sby -f sram_controller.sby cover

sram_controller_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
