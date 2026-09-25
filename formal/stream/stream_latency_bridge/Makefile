# SPDX-License-Identifier: MIT
# Formal verification Makefile for stream_latency_bridge
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
#
# BUG-001: this unit used to read a hand-copied `gaxi_fifo_sync_formal.sv`
# (155 lines against the real module's 250, 133 differing) instead of the RTL
# that ships. The fork existed because yosys cannot elaborate
# `parameter fifo_mem_t MEM_STYLE = FIFO_AUTO` (gaxi_fifo_sync.sv:27) once
# stream_latency_bridge instantiates it with .MEM_STYLE(FIFO_AUTO) -- note
# that reading the module STANDALONE succeeds; it is DERIVE mode that fails,
# which is why a shallow test says the fork is unnecessary when it is not.
#
# sv2v resolves the package-typed parameter, so the fork is not needed:
# flatten the real RTL. See vault BUG-001 and handbook dv/formal.md,
# "PROVING A FORK IS WORSE THAN NO PROOF".

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

# Closed set: stream_latency_bridge instantiates only gaxi_fifo_sync, and
# counter_bin/fifo_control instantiate nothing.
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv

DUT := $(REPO_ROOT)/projects/components/dmas/stream/rtl/fub/stream_latency_bridge.sv

.PHONY: prove cover clean

prove: stream_latency_bridge_flat.v
	sby -f stream_latency_bridge.sby prove

cover: stream_latency_bridge_flat.v
	sby -f stream_latency_bridge.sby cover

stream_latency_bridge_flat.v: $(DUT) $(DEPS)
	$(SV2V) $(INC) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
