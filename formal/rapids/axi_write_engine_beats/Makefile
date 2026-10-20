# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi_write_engine_beats (RAPIDS fub_beats)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := axi_write_engine_beats_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/dma-ip/rapids/rtl/filelists/fub_beats/axi_write_engine_beats.f
# sv2v does not honour `// synopsys translate_off`, so the write engine's
# hang-diagnostic $display would survive into the flat, and yosys cannot
# size its $time argument (AST_AUTOWIRE). Stripped for FORMAL only;
# simulation reads the original source and keeps the prints.
FLAT_PREP       := /synopsys translate_off/,/synopsys translate_on/d
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean

prove: axi_write_engine_beats_flat.v
	sby -f axi_write_engine_beats.sby prove

cover: axi_write_engine_beats_flat.v
	sby -f axi_write_engine_beats.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover $(FLAT_BUILD)
