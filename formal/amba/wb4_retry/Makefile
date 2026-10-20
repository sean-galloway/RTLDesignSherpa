# SPDX-License-Identifier: MIT
# Formal verification Makefile for wb4_retry
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
# (same shape as formal/amba/wb4_master/Makefile).

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := wb4_retry_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/amba/filelists/wb4_retry.f
# --define=FORMAL keeps the in-RTL formal blocks; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (vault/handbook/dv/formal.md).
FLAT_SV2V_FLAGS := --define=FORMAL --exclude=Assert
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover prove_deep cover_deep all clean

all: prove cover prove_deep cover_deep

prove: wb4_retry_flat.v
	sby -f wb4_retry.sby prove

cover: wb4_retry_flat.v
	sby -f wb4_retry.sby cover

# INFLIGHT=2 via chparam on the harness top: the count bounds and the
# in-order hand-back with two entries open.
prove_deep: wb4_retry_flat.v
	sby -f wb4_retry.sby prove_deep

cover_deep: wb4_retry_flat.v
	sby -f wb4_retry.sby cover_deep

clean:
	rm -rf *_flat.v *_prove *_cover *_prove_deep *_cover_deep
