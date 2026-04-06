# SPDX-License-Identifier: MIT
# Formal verification Makefile for descriptor_engine
# Workflow: sv2v flattens SystemVerilog -> patch multi-driver -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(REPO_ROOT)/projects/components/stream/rtl/includes

# Package files (order matters: dependencies first)
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_arbiter_pkg.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/includes/stream_pkg.sv

# RTL dependencies (descriptor_engine uses gaxi_fifo_sync + gaxi_skid_buffer)
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/stream/rtl/fub/descriptor_engine.sv

# Post-processing script to fix multi-driver issues in sv2v output.
# The RTL has two always_ff blocks driving r_descriptor_error (main FSM +
# separate APB address-0 check). sv2v emits both as independent always blocks,
# which yosys rejects as multiple drivers. The patch script merges the second
# block into the main FSM block.
PATCH := python3 $(CURDIR)/patch_flat.py

.PHONY: prove cover clean

prove: descriptor_engine_flat.v
	sby -f descriptor_engine.sby prove

cover: descriptor_engine_flat.v
	sby -f descriptor_engine.sby cover

descriptor_engine_flat.v: $(DUT) $(PKGS) $(DEPS) patch_flat.py
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@.raw
	$(PATCH) $@.raw $@
	rm -f $@.raw

clean:
	rm -rf *_flat.v *.raw *_prove *_cover
