# SPDX-License-Identifier: MIT
# Formal verification Makefile for perf_profiler
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(REPO_ROOT)/projects/components/stream/rtl/includes

# Package files (order matters: dependencies first)
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/includes/stream_pkg.sv

# RTL dependencies (FIFO and counter submodules)
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/stream/rtl/fub/perf_profiler.sv

.PHONY: prove cover clean

prove: perf_profiler_flat.v
	sby -f perf_profiler.sby prove

cover: perf_profiler_flat.v
	sby -f perf_profiler.sby cover

perf_profiler_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
