# SPDX-License-Identifier: MIT
# Formal verification Makefile for scheduler
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := scheduler_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/dma-ip/stream/rtl/filelists/fub/scheduler.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean

prove: scheduler_flat.v
	sby -f scheduler.sby prove

cover: scheduler_flat.v
	sby -f scheduler.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
