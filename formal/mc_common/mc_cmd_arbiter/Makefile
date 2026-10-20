# SPDX-License-Identifier: MIT
# Formal verification Makefile for pumice_cmd_arbiter COMPOSED with global_timers.
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# Both modules are flattened together because the proof is about the LOOP
# between them -- see formal_cmd_arbiter.sv.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := arb_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_global_timers.f \
                   $(REPO_ROOT)/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_cmd_arbiter.f
# mc_cmd_arbiter's always_comb blocks read whole unpacked arrays; sv2v spells
# each as an explicit `always @(a or b ...)` list naming them, which yosys
# rejects ("Insufficient number of array indices"). A combinational list
# means nothing to yosys, so every non-edge list is rewritten to @(*).
COMB_STAR := sed -E '/(posedge|negedge)/!s/^([[:space:]]*)always @\(.*\) begin$$/\1always @(*) begin/'
FLAT_POST       := $(COMB_STAR)
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove issue019 cover all clean
# `issue019` was the held-red reproduction for pumice BUG-021 (the tRRD/tFAW
# fire-stage gap). The gap is fixed -- w_out_safe re-checks the rank-global
# windows live at the fire -- and the .sby now arms the ISSUE019 assertions for
# every task, so `prove` (and the formal/mc_common area dispatch) guards the fix
# directly. `make issue019` stays as a named entry point to the same armed
# task.
all: prove cover
prove: arb_flat.v
	sby -f cmd_arbiter.sby prove
issue019: arb_flat.v
	sby -f cmd_arbiter.sby issue019

cover: arb_flat.v
	sby -f cmd_arbiter.sby cover

clean:
	rm -rf *_flat.v arb_flat.v cmd_arbiter_prove cmd_arbiter_issue019 cmd_arbiter_cover
