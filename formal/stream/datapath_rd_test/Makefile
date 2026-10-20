# SPDX-License-Identifier: MIT
# Formal verification Makefile for datapath_rd_test
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := datapath_rd_test_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/dma-ip/stream/rtl/filelists/macro/datapath_rd_test.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean

prove: datapath_rd_test_flat.v
	sby -f datapath_rd_test.sby prove

cover: datapath_rd_test_flat.v
	sby -f datapath_rd_test.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
