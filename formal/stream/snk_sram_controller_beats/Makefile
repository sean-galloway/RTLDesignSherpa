# SPDX-License-Identifier: MIT
# Formal verification Makefile for snk_sram_controller_beats (RAPIDS macro_beats)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(REPO_ROOT)/projects/components/rapids/rtl/includes

# RTL dependencies (all of snk_sram_controller_unit_beats deps plus the unit itself)
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/projects/components/rapids/rtl/fub_beats/alloc_ctrl_beats.sv \
        $(REPO_ROOT)/projects/components/rapids/rtl/fub_beats/drain_ctrl_beats.sv \
        $(REPO_ROOT)/projects/components/rapids/rtl/fub_beats/latency_bridge_beats.sv \
        $(REPO_ROOT)/projects/components/rapids/rtl/macro_beats/snk_sram_controller_unit_beats.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/rapids/rtl/macro_beats/snk_sram_controller_beats.sv

.PHONY: prove cover clean

prove: snk_sram_controller_beats_flat.v
	sby -f snk_sram_controller_beats.sby prove

cover: snk_sram_controller_beats_flat.v
	sby -f snk_sram_controller_beats.sby cover

snk_sram_controller_beats_flat.v: $(DUT) $(DEPS)
	$(SV2V) $(INC) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
