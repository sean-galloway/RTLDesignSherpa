# SPDX-License-Identifier: MIT
# Formal verification Makefile for snk_sram_controller_beats (RAPIDS macro_beats)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
#
# snk_sram_controller_beats is a NAMING WRAPPER around STREAM's sram_controller,
# so the dependency closure is STREAM's SRAM files, not RAPIDS' former
# snk_sram_controller_unit_beats + alloc/drain/latency_bridge_beats copies.
# None of STREAM's five SRAM files references stream_pkg (measured: 0 refs), so
# no package files are needed here.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := snk_sram_controller_beats_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/dma-ip/rapids/rtl/filelists/macro_beats/snk_sram_controller_beats.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean

prove: snk_sram_controller_beats_flat.v
	sby -f snk_sram_controller_beats.sby prove

cover: snk_sram_controller_beats_flat.v
	sby -f snk_sram_controller_beats.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
