# SPDX-License-Identifier: MIT
# Formal verification Makefile for scheduler_group
# Integration wrapper: descriptor_engine + scheduler + monbus_arbiter
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := scheduler_group_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/dma-ip/stream/rtl/filelists/macro/scheduler_group.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean

prove: scheduler_group_flat.v
	sby -f scheduler_group.sby prove

cover: scheduler_group_flat.v
	sby -f scheduler_group.sby cover

clean:
	rm -rf *_flat.v *.raw *_prove *_cover
