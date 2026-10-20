# SPDX-License-Identifier: MIT
# Formal verification Makefile for l1_control
# Workflow: sv2v flattens the REAL RTL -> sby reads plain Verilog (plain prep).
#
# Closure: l1_pkg + l1_pending_fill_bypass + l1_victim (the two leaf
# sub-blocks control instantiates) + l1_control. The tag/data/repl arrays
# stay outside: the wrapper models the tag store abstractly and frees the
# rest (see formal_amber_control.sv).
# Geometry: the tiny formal configuration SETS=16 / WAYS=2 / 64B / 64b.
# Regenerate the flat file whenever the RTL changes.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := amber_control_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/cache-ip/common-ip/rtl/filelists/l1_control.f
# --define=FORMAL keeps the in-RTL formal blocks; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (vault/handbook/dv/formal.md).
FLAT_SV2V_FLAGS := --define=FORMAL --exclude=Assert
# specialize_params pins the tiny formal geometry AND deletes the parameter
# declarations, so the DUT is parameterless and yosys's expose applies
# (bind silently never fires in this yosys build).
FLAT_POST       := python3 ../specialize_params.py - /dev/stdout --param ADDR_WIDTH=32 --param SETS=16 --param WAYS=2 --param LINE_BYTES=64 --param BUS_WIDTH=64 --param PF_GUARD=0 --module l1_control
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove prove-live cover all clean

all: prove prove-live cover

prove: amber_control_flat.v
	sby -f amber_control.sby prove

# bounded-liveness (no deadlock/livelock) -- model-free wrapper, BMC
prove-live: amber_control_flat.v
	sby -f amber_control_live.sby prove

cover: amber_control_flat.v
	sby -f amber_control.sby cover

clean:
	rm -rf amber_control_prove amber_control_cover amber_control_live_prove
