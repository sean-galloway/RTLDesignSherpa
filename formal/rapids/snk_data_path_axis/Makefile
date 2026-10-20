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

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := snk_data_path_axis_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/dma-ip/rapids/rtl/filelists/macro/snk_data_path_axis.f
# sv2v does not honour `// synopsys translate_off`, so the write engine's
# hang-diagnostic $display would survive into the flat, and yosys cannot
# size its $time argument (AST_AUTOWIRE). Stripped for FORMAL only;
# simulation reads the original source and keeps the prints.
FLAT_PREP       := /synopsys translate_off/,/synopsys translate_on/d
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean

prove: snk_data_path_axis_flat.v
	sby -f snk_data_path_axis.sby prove

cover: snk_data_path_axis_flat.v
	sby -f snk_data_path_axis.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover $(FLAT_BUILD)
