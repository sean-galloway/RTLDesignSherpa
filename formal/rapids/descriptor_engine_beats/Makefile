# SPDX-License-Identifier: MIT
# Formal verification Makefile for descriptor_engine_beats (RAPIDS fub_beats variant)
# Workflow: sv2v flattens SystemVerilog -> patch multi-driver -> sby reads plain Verilog

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := descriptor_engine_beats_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/dma-ip/rapids/rtl/filelists/fub_beats/descriptor_engine_beats.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean

prove: descriptor_engine_beats_flat.v
	sby -f descriptor_engine_beats.sby prove

cover: descriptor_engine_beats_flat.v
	sby -f descriptor_engine_beats.sby cover

clean:
	rm -rf *_flat.v *.raw *_prove *_cover
