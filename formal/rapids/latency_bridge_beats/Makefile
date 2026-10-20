# SPDX-License-Identifier: MIT
# Formal verification Makefile for latency_bridge_beats (RAPIDS fub_beats)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := latency_bridge_beats_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/dma-ip/rapids/rtl/filelists/fub_beats/latency_bridge_beats.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean

prove: latency_bridge_beats_flat.v
	sby -f latency_bridge_beats.sby prove

cover: latency_bridge_beats_flat.v
	sby -f latency_bridge_beats.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
