# SPDX-License-Identifier: MIT
# Formal verification for scoria_cmd_arbiter COMPOSED with scoria_global_timers.
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# Both modules are flattened together because the proof is about the LOOP
# between them -- see formal_scoria_cmd_arbiter.sv.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := arb_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_global_timers.f \
                   $(REPO_ROOT)/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_cmd_arbiter.f
# mc_cmd_arbiter's always_comb blocks read whole unpacked arrays; sv2v spells
# each as an explicit `always @(a or b ...)` list naming them, which yosys
# rejects ("Insufficient number of array indices"). A combinational list
# means nothing to yosys, so every non-edge list is rewritten to @(*).
COMB_STAR := sed -E '/(posedge|negedge)/!s/^([[:space:]]*)always @\(.*\) begin$$/\1always @(*) begin/'
FLAT_POST       := $(COMB_STAR)
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove nofix cover all clean
# `all` deliberately excludes nofix: that task re-proves the PRE-FIX gate and
# is expected to FAIL. It is what makes the passing proof mean something, and
# it is not a regression signal.
all: prove cover

prove: arb_flat.v
	sby -f scoria_cmd_arbiter.sby prove

# The BUG-001 properties disarmed. Only useful paired with a reverted gate --
# on the fixed RTL this proves strictly less than `prove`.
nofix: arb_flat.v
	sby -f scoria_cmd_arbiter.sby nofix

cover: arb_flat.v
	sby -f scoria_cmd_arbiter.sby cover

clean:
	rm -rf *_flat.v arb_flat.v scoria_cmd_arbiter_prove \
	       scoria_cmd_arbiter_nofix scoria_cmd_arbiter_cover
