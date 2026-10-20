# SPDX-License-Identifier: MIT
# Formal verification Makefile for ctrlwr_engine (RAPIDS control engine, Phase 2)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# Modelled on descriptor_engine_beats: the engine imports the monitor packages
# through rapids_imports.svh, so the same package list and ocelus_pkg stub apply.
REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := ctrlwr_engine_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/dma-ip/rapids/rtl/filelists/fub/ctrlwr_engine.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean
prove: ctrlwr_engine_flat.v
	sby -f ctrlwr_engine.sby prove
cover: ctrlwr_engine_flat.v
	sby -f ctrlwr_engine.sby cover
clean:
	rm -rf *_flat.v *_prove *_cover
