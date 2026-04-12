# SPDX-License-Identifier: MIT
# Formal verification Makefile for scheduler_group
# Integration wrapper: descriptor_engine + scheduler + monbus_arbiter
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

# RTL dependencies (full transitive closure)
# descriptor_engine deps: gaxi_fifo_sync, gaxi_skid_buffer, counter_bin, fifo_control
# scheduler deps: none (pure logic + FSM)
# monbus_arbiter deps: arbiter_round_robin, arbiter_priority_encoder, gaxi_skid_buffer
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/common/arbiter_round_robin.sv \
        $(REPO_ROOT)/rtl/common/arbiter_priority_encoder.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv \
        $(REPO_ROOT)/rtl/amba/shared/monbus_arbiter.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/descriptor_engine.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/fub/scheduler.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/stream/rtl/macro/scheduler_group.sv

# Post-processing script to fix multi-driver issues in sv2v output.
# The descriptor_engine RTL (instantiated inside scheduler_group) has two
# always_ff blocks driving r_descriptor_error (main FSM + APB address check).
# Same fix as formal/stream/descriptor_engine/patch_flat.py.
PATCH := python3 $(CURDIR)/patch_flat.py

.PHONY: prove cover clean

prove: scheduler_group_flat.v
	sby -f scheduler_group.sby prove

cover: scheduler_group_flat.v
	sby -f scheduler_group.sby cover

scheduler_group_flat.v: $(DUT) $(PKGS) $(DEPS) patch_flat.py
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@.raw
	$(PATCH) $@.raw $@
	rm -f $@.raw

clean:
	rm -rf *_flat.v *.raw *_prove *_cover
