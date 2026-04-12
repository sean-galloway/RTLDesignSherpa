# SPDX-License-Identifier: MIT
# Formal verification Makefile for datapath_wr_test
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(REPO_ROOT)/projects/components/stream/rtl/includes

# Package files (order matters: dependencies first)
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_arbiter_pkg.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/includes/stream_pkg.sv

# RTL dependencies (transitive closure for datapath_wr_test):
#   datapath_wr_test -> scheduler (no sub-deps)
#                    -> axi_write_engine -> arbiter_round_robin, arbiter_priority_encoder
#                                        -> gaxi_fifo_sync -> counter_bin, fifo_control
#                    -> sram_controller -> sram_controller_unit
#                                       -> stream_alloc_ctrl, stream_drain_ctrl
#                                       -> stream_latency_bridge -> gaxi_fifo_sync
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/common/arbiter_round_robin.sv \
        $(REPO_ROOT)/rtl/common/arbiter_priority_encoder.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/stream_alloc_ctrl.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/stream_drain_ctrl.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/stream_latency_bridge.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/sram_controller_unit.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/sram_controller.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/scheduler.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/axi_write_engine.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/stream/rtl/macro/datapath_wr_test.sv

.PHONY: prove cover clean

prove: datapath_wr_test_flat.v
	sby -f datapath_wr_test.sby prove

cover: datapath_wr_test_flat.v
	sby -f datapath_wr_test.sby cover

datapath_wr_test_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
