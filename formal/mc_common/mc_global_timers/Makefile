# SPDX-License-Identifier: MIT
# Formal verification Makefile for global_timers (pumice)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := global_timers_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_global_timers.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: global_timers_flat.v
	sby -f global_timers.sby prove

cover: global_timers_flat.v
	sby -f global_timers.sby cover

clean:
	rm -rf *_flat.v global_timers_prove global_timers_cover
