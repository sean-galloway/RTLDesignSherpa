# SPDX-License-Identifier: MIT
# Formal verification Makefile for uart_axil_bridge
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
# Dependencies: uart_rx, uart_tx, axil4_master_rd, axil4_master_wr, gaxi_skid_buffer

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := uart_axil_bridge_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/utility-ip/converters/rtl/filelists/uart_axil_bridge.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: uart_axil_bridge_flat.v
	sby -f uart_axil_bridge.sby prove

cover: uart_axil_bridge_flat.v
	sby -f uart_axil_bridge.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
