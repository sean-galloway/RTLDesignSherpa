# SPDX-License-Identifier: MIT
# Formal verification Makefile for pumice_cmd_arbiter COMPOSED with global_timers.
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# Both modules are flattened together because the proof is about the LOOP
# between them -- see formal_cmd_arb_frfcfs.sv.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := cmd_arb_frfcfs_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_global_timers.f \
                   $(REPO_ROOT)/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_cmd_arb_frfcfs.f
# mc_cmd_arb_frfcfs's always_comb blocks read whole unpacked arrays; sv2v spells
# each as an explicit `always @(a or b ...)` list naming them, which yosys
# rejects ("Insufficient number of array indices"). A combinational list
# means nothing to yosys, so every non-edge list is rewritten to @(*).
COMB_STAR := sed -E '/(posedge|negedge)/!s/^([[:space:]]*)always @\(.*\) begin$$/\1always @(*) begin/'
FLAT_POST       := $(COMB_STAR)
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: dual_cover prove issue019 cover all clean
# `issue019` was the held-red reproduction for pumice BUG-021 (the tRRD/tFAW
# fire-stage gap). The gap is fixed -- w_out_safe re-checks the rank-global
# windows live at the fire -- and the .sby now arms the ISSUE019 assertions for
# every task, so `prove` (and the formal/mc_common area dispatch) guards the fix
# directly. `make issue019` stays as a named entry point to the same armed
# task.
all: prove cover
prove: cmd_arb_frfcfs_flat.v
	sby -f cmd_arb_frfcfs.sby prove
issue019: cmd_arb_frfcfs_flat.v
	sby -f cmd_arb_frfcfs.sby issue019

cover: cmd_arb_frfcfs_flat.v
	sby -f cmd_arb_frfcfs.sby cover

# TASK-047 row lane (DUAL_ISSUE): bmc + cover with the lane built
dual_cover: cmd_arb_frfcfs_flat.v
	sby -f cmd_arb_frfcfs.sby dual_cover

dual: cmd_arb_frfcfs_flat.v
	sby -f cmd_arb_frfcfs.sby dual dual_cover

clean:
	rm -rf *_flat.v cmd_arb_frfcfs_flat.v cmd_arb_frfcfs_prove cmd_arb_frfcfs_issue019 cmd_arb_frfcfs_cover
