# SPDX-License-Identifier: MIT
# Formal verification Makefile for snk_data_path_axis (RAPIDS macro, byte tree)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
#
# The DUT is the whole byte sink chain: snk_data_path_axis -> snk_data_path ->
# {snk_sram_controller (a naming wrapper around STREAM's sram_controller),
# axi_write_engine}. So the dependency closure is RAPIDS macro + the byte
# write engine + STREAM's five SRAM files.
#
# Solver: smtbmc bitwuzla -- z3 dies on the SRAM arrays (measured 2026-10-02:
# stuck ~step 15 at a 30-min cap, cooperative slave). Measured budget with the
# full shadow state: per-step cost explodes past step 12 (~16 min at step 14
# on a loaded box), so prove depth is pinned to 15 -- sby `depth N` checks
# steps 0..N-1, and step 14 is both the deepest cover witness (cp_kill_inflight)
# and the deepest mutation-CEX step observed in the 7-break battery, so depth
# 14 leaves exactly one step of witness/CEX out of budget (see the .sby for
# the full note). The /tmp probe figure sometimes
# cited (depth 50 in 38 s) was the bare closure with free inputs -- it does
# not survive contact with the shadow packet queue and expectation FIFO.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
TMPDIR    := .sv2v_prep

RAPIDS := $(REPO_ROOT)/projects/components/dma-ip/rapids
STREAM := $(REPO_ROOT)/projects/components/dma-ip/stream

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(RAPIDS)/rtl/includes

# Package files (order matters: dependencies first). Real monitor_pkg flattens
# clean for this closure (measured); the ctrlrd_engine stub is the fallback.
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba5_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_arbiter_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_pkg.sv \
        $(RAPIDS)/rtl/includes/rapids_pkg.sv

# RTL dependencies, in compile order. arbiter_single_client is used by the
# byte axi_write_engine's NC==1 generate branch (the beats twin did not).
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
        $(RAPIDS)/rtl/macro/snk_sram_controller.sv \
        $(RAPIDS)/rtl/macro/snk_data_path.sv

# Device under test (the sed-prepped write engine joins DUT_PREP below)
DUT := $(RAPIDS)/rtl/macro/snk_data_path_axis.sv

.PHONY: prove cover clean

prove: snk_data_path_axis_flat.v
	sby -f snk_data_path_axis.sby prove

cover: snk_data_path_axis_flat.v
	sby -f snk_data_path_axis.sby cover

# sv2v does not honour `// synopsys translate_off` -- it is a comment to sv2v,
# so the hang-diagnostic $display in axi_write_engine survives into the flat
# and yosys cannot size its $time argument. Strip those blocks for FORMAL
# ONLY (recipe copied from axi_write_engine_beats). Only the write engine
# needs it -- measured 2026-10-02: no other file in this closure has
# translate_off that reaches the flat (stream_drain_ctrl's is `synthesis
# translate_off`, which the snk_sram_controller_beats proof passes unstripped).
ENG_PREP := $(TMPDIR)/axi_write_engine.sv

$(TMPDIR):
	mkdir -p $(TMPDIR)

$(ENG_PREP): $(RAPIDS)/rtl/fub/axi_write_engine.sv | $(TMPDIR)
	sed '/synopsys translate_off/,/synopsys translate_on/d' $< > $@

snk_data_path_axis_flat.v: $(DUT) $(ENG_PREP) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(ENG_PREP) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover $(TMPDIR)

# tooling TASK-026: regenerate-and-diff self-detection for the committed flat.
# House pattern from formal/common/counter_freq_invariant; consumed by
# bin/formal_status.py --check-flats (mechanism a) and the pre-commit gate.
# Comparison squeezes whitespace, matching the token normalization the
# checker uses (committed flats may be post-formatter).
.PHONY: check-flat .check_flat_tmp
check-flat: .check_flat_tmp
	@if [ "$$(tr -s '[:space:]' ' ' < .check_flat_tmp)" = "$$(tr -s '[:space:]' ' ' < snk_data_path_axis_flat.v)" ]; then \
		rm -f .check_flat_tmp; \
		echo "flat file is current"; \
	else \
		rm -f .check_flat_tmp; \
		echo "STALE: snk_data_path_axis_flat.v does not match the RTL."; \
		echo "Regenerate with: make snk_data_path_axis_flat.v"; \
		exit 1; \
	fi

.check_flat_tmp: $(DUT) $(ENG_PREP) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(ENG_PREP) $(DUT) > $@