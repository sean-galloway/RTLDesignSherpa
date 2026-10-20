# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi4_dwidth_converter_rd
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := axi4_dwidth_converter_rd_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/utility-ip/converters/rtl/filelists/axi4_dwidth_converter_rd.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean

prove: axi4_dwidth_converter_rd_flat.v
	sby -f axi4_dwidth_converter_rd.sby prove

cover: axi4_dwidth_converter_rd_flat.v
	sby -f axi4_dwidth_converter_rd.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
