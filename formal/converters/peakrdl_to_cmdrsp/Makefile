# SPDX-License-Identifier: MIT
# Formal verification Makefile for peakrdl_to_cmdrsp
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := peakrdl_to_cmdrsp_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/utility-ip/converters/rtl/filelists/peakrdl_to_cmdrsp.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: peakrdl_to_cmdrsp_flat.v
	sby -f peakrdl_to_cmdrsp.sby prove

cover: peakrdl_to_cmdrsp_flat.v
	sby -f peakrdl_to_cmdrsp.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
