# SPDX-License-Identifier: MIT
# Formal verification Makefile for scheduler
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(REPO_ROOT)/projects/components/dmas/stream/rtl/includes

# Package files (order matters: dependencies first)
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_arbiter_pkg.sv \
        $(REPO_ROOT)/projects/components/dmas/stream/rtl/includes/stream_pkg.sv

# RTL dependencies. The old comment here said "scheduler is pure logic + FSM,
# no submodule instantiations" -- that stopped being true when scheduler gained
# stream_run_addr_gen under USE_ROW_COL_MAJOR_ADDRESSING, which DEFAULTS TO 1
# (scheduler.sv:87). Without these the proof dies at elaboration.
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/projects/components/misc/rtl/dma_address_gen.sv \
        $(REPO_ROOT)/projects/components/misc/rtl/stream_run_addr_gen.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/dmas/stream/rtl/fub/scheduler.sv

.PHONY: prove cover clean

prove: scheduler_flat.v
	sby -f scheduler.sby prove

cover: scheduler_flat.v
	sby -f scheduler.sby cover

scheduler_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
