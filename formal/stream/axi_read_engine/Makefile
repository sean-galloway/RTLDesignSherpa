# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi_read_engine
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(REPO_ROOT)/projects/components/stream/rtl/includes

# Package files (order matters: dependencies first)
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/includes/stream_pkg.sv

# RTL dependencies
DEPS := $(REPO_ROOT)/rtl/common/arbiter_round_robin.sv \
        $(REPO_ROOT)/rtl/common/arbiter_priority_encoder.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/stream/rtl/fub/axi_read_engine.sv

.PHONY: prove cover clean

prove: axi_read_engine_flat.v
	sby -f axi_read_engine.sby prove

cover: axi_read_engine_flat.v
	sby -f axi_read_engine.sby cover

axi_read_engine_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
