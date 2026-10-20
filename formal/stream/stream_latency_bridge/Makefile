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

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := stream_latency_bridge_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/dma-ip/stream/rtl/filelists/fub/stream_latency_bridge.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean

prove: stream_latency_bridge_flat.v
	sby -f stream_latency_bridge.sby prove

cover: stream_latency_bridge_flat.v
	sby -f stream_latency_bridge.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
