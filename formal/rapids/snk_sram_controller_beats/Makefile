# SPDX-License-Identifier: MIT
# Formal verification Makefile for snk_sram_controller_beats (RAPIDS macro_beats)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
#
# snk_sram_controller_beats is a NAMING WRAPPER around STREAM's sram_controller,
# so the dependency closure is STREAM's SRAM files, not RAPIDS' former
# snk_sram_controller_unit_beats + alloc/drain/latency_bridge_beats copies.
# None of STREAM's five SRAM files references stream_pkg (measured: 0 refs), so
# no package files are needed here.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v

# Include paths for sv2v preprocessing (fifo_defs.svh + reset_defs.svh both live here)
INC := -I$(REPO_ROOT)/rtl/amba/includes

# RTL dependencies: STREAM's SRAM implementation, in compile order
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/projects/components/dmas/stream/rtl/fub/stream_alloc_ctrl.sv \
        $(REPO_ROOT)/projects/components/dmas/stream/rtl/fub/stream_drain_ctrl.sv \
        $(REPO_ROOT)/projects/components/dmas/stream/rtl/fub/stream_latency_bridge.sv \
        $(REPO_ROOT)/projects/components/dmas/stream/rtl/fub/sram_controller_unit.sv \
        $(REPO_ROOT)/projects/components/dmas/stream/rtl/fub/sram_controller.sv

# Device under test (the RAPIDS naming wrapper)
DUT := $(REPO_ROOT)/projects/components/dmas/rapids/rtl/macro_beats/snk_sram_controller_beats.sv

.PHONY: prove cover clean

prove: snk_sram_controller_beats_flat.v
	sby -f snk_sram_controller_beats.sby prove

cover: snk_sram_controller_beats_flat.v
	sby -f snk_sram_controller_beats.sby cover

snk_sram_controller_beats_flat.v: $(DUT) $(DEPS)
	$(SV2V) $(INC) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
