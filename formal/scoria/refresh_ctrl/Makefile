# SPDX-License-Identifier: MIT
# Formal verification Makefile for scoria_refresh_ctrl
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := refresh_ctrl_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/rtl/filelists/fub/scoria_refresh_ctrl.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: refresh_ctrl_flat.v
	sby -f scoria_refresh_ctrl.sby prove

cover: refresh_ctrl_flat.v
	sby -f scoria_refresh_ctrl.sby cover

clean:
	rm -rf *_flat.v refresh_ctrl_prove refresh_ctrl_cover
