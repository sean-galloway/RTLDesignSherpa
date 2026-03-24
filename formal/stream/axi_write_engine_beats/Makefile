# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi_write_engine_beats (RAPIDS fub_beats)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(REPO_ROOT)/projects/components/rapids/rtl/includes

# Package files (order matters: dependencies first)
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba5_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_arbiter_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_pkg.sv \
        $(REPO_ROOT)/projects/components/rapids/rtl/includes/rapids_pkg.sv

# RTL dependencies (write engine uses gaxi_fifo_sync which needs counter_bin + fifo_control)
DEPS := $(REPO_ROOT)/rtl/common/arbiter_round_robin.sv \
        $(REPO_ROOT)/rtl/common/arbiter_priority_encoder.sv \
        $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/rapids/rtl/fub_beats/axi_write_engine_beats.sv

.PHONY: prove cover clean

prove: axi_write_engine_beats_flat.v
	sby -f axi_write_engine_beats.sby prove

cover: axi_write_engine_beats_flat.v
	sby -f axi_write_engine_beats.sby cover

axi_write_engine_beats_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
