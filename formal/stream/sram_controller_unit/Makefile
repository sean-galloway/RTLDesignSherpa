# SPDX-License-Identifier: MIT
# Formal verification Makefile for sram_controller_unit
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := sram_controller_unit_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/dma-ip/stream/rtl/filelists/fub/sram_controller_unit.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean

prove: sram_controller_unit_flat.v
	sby -f sram_controller_unit.sby prove

cover: sram_controller_unit_flat.v
	sby -f sram_controller_unit.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
