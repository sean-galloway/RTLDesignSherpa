# SPDX-License-Identifier: MIT
# Formal verification Makefile for scoria_addr_mapper
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := addr_mapper_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_addr_mapper.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: addr_mapper_flat.v
	sby -f scoria_addr_mapper.sby prove

cover: addr_mapper_flat.v
	sby -f scoria_addr_mapper.sby cover

clean:
	rm -rf *_flat.v addr_mapper_prove addr_mapper_cover
