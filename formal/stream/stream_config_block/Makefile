# SPDX-License-Identifier: MIT
# Formal verification Makefile for stream_config_block
# Pure combinational module (assigns only), but uses `include "reset_defs.svh"
# so we run sv2v to strip the include and produce plain Verilog.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := stream_config_block_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/dma-ip/stream/rtl/filelists/top/stream_config_block.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean

prove: stream_config_block_flat.v
	sby -f stream_config_block.sby prove

cover: stream_config_block_flat.v
	sby -f stream_config_block.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
