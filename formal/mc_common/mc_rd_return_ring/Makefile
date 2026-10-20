# SPDX-License-Identifier: MIT
# Formal verification Makefile for pumice_rd_return_ring
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := ring_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_rd_return_ring.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove data cover all clean

all: prove cover

# `prove` runs BOTH safety tasks. The split between them is a SOLVER-COST split,
# not a semantic one -- data integrity is a safety property like the rest -- so
# an area-level `make prove-rd_return_ring` must not silently skip it. `data`
# stays as a separate target for iterating on just that family.
prove: ring_flat.v
	sby -f rd_return_ring.sby prove
	sby -f rd_return_ring.sby data

data: ring_flat.v
	sby -f rd_return_ring.sby data

cover: ring_flat.v
	sby -f rd_return_ring.sby cover

clean:
	rm -rf *_flat.v ring_flat.v rd_return_ring_prove rd_return_ring_data rd_return_ring_cover
