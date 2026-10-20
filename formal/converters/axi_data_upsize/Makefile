# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi_data_upsize
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := axi_data_upsize_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/utility-ip/converters/rtl/filelists/axi_data_upsize.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: axi_data_upsize_flat.v
	sby -f axi_data_upsize.sby prove

cover: axi_data_upsize_flat.v
	sby -f axi_data_upsize.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
