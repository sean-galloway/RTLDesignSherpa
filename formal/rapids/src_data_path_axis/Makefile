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

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := src_data_path_axis_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/dma-ip/rapids/rtl/filelists/macro/src_data_path_axis.f
# sv2v does not honour `// synopsys translate_off`, so the write engine's
# hang-diagnostic $display would survive into the flat, and yosys cannot
# size its $time argument (AST_AUTOWIRE). Stripped for FORMAL only;
# simulation reads the original source and keeps the prints.
FLAT_PREP       := /synopsys translate_off/,/synopsys translate_on/d
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean

prove: src_data_path_axis_flat.v
	sby -f src_data_path_axis.sby prove

cover: src_data_path_axis_flat.v
	sby -f src_data_path_axis.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover $(FLAT_BUILD)
