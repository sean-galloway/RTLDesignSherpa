# SPDX-License-Identifier: MIT
# Formal Verification Makefile for src_data_path_axis (RAPIDS macro, byte tree)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
#
# The DUT is the whole byte source chain: AXIS egress shifter + packet-record
# queue + drain allocator -> src_data_path -> {src_sram_controller (a naming
# wrapper around STREAM's sram_controller), axi_read_engine}. So the dependency
# closure is RAPIDS macro + the byte read engine + STREAM's five SRAM files.
# Mirror of the snk_data_path_axis unit (TASK-022 DIR 1); differences: the
# engine is axi_read_engine (NO translate_off strip needed -- measured
# 2026-10-03: no synopsys translate_off blocks, no $display/$time), and
# src_sram_controller stores DATA_WIDTH(DW) with no byte enables (read side
# has no WSTRB).
#
# Solver: smtbmc bitwuzla -- z3 dies on the SRAM arrays (measured 2026-10-02
# on the sink closure). Prove depth lives in the .sby and is pinned by the
# depth sweep (TASK-022 DIR 2, Task 6); per-step budget notes land there.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
TMPDIR    := .sv2v_prep

RAPIDS := $(REPO_ROOT)/projects/components/dma-ip/rapids
STREAM := $(REPO_ROOT)/projects/components/dma-ip/stream

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(RAPIDS)/rtl/includes

# Package files (order matters: dependencies first), same set as the sink
# closure (rapids_imports.svh wildcard-imports monitor_common/monitor_amba4/
# monitor_arbiter/rapids_pkg; monitor_pkg flattens clean for this closure).
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba5_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_arbiter_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_pkg.sv \
        $(RAPIDS)/rtl/includes/rapids_pkg.sv

# RTL dependencies, in compile order. arbiter_single_client is used by the
# byte axi_read_engine's NC==1 generate branch (the beats twin did not),
# same as the sink closure.
DEPS := $(REPO_ROOT)/rtl/common/arbiter_priority_encoder.sv \
        $(REPO_ROOT)/rtl/common/arbiter_round_robin.sv \
        $(REPO_ROOT)/rtl/common/arbiter_single_client.sv \
        $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(STREAM)/rtl/fub/stream_alloc_ctrl.sv \
        $(STREAM)/rtl/fub/stream_drain_ctrl.sv \
        $(STREAM)/rtl/fub/stream_latency_bridge.sv \
        $(STREAM)/rtl/fub/sram_controller_unit.sv \
        $(STREAM)/rtl/fub/sram_controller.sv \
        $(RAPIDS)/rtl/macro/src_sram_controller.sv \
        $(RAPIDS)/rtl/macro/src_data_path.sv \
        $(RAPIDS)/rtl/fub/axi_read_engine.sv

# Device under test (the byte read engine is passed explicitly, after
# src_data_path, same position ENG_PREP held in the sink unit).
DUT := $(RAPIDS)/rtl/macro/src_data_path_axis.sv

.PHONY: prove cover clean

prove: src_data_path_axis_flat.v
	sby -f src_data_path_axis.sby prove

cover: src_data_path_axis_flat.v
	sby -f src_data_path_axis.sby cover

src_data_path_axis_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover $(TMPDIR)

# tooling TASK-026: regenerate-and-diff self-detection for the committed flat.
# House pattern from formal/common/counter_freq_invariant; consumed by
# bin/formal_status.py --check-flats (mechanism a) and the pre-commit gate.
# Comparison squeezes whitespace, matching the token normalization the
# checker uses (committed flats may be post-formatter).
.PHONY: check-flat .check_flat_tmp
check-flat: .check_flat_tmp
	@if [ "$$(tr -s '[:space:]' ' ' < .check_flat_tmp)" = "$$(tr -s '[:space:]' ' ' < src_data_path_axis_flat.v)" ]; then \
		rm -f .check_flat_tmp; \
		echo "flat file is current"; \
	else \
		rm -f .check_flat_tmp; \
		echo "STALE: src_data_path_axis_flat.v does not match the RTL."; \
		echo "Regenerate with: make src_data_path_axis_flat.v"; \
		exit 1; \
	fi

.check_flat_tmp: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@
