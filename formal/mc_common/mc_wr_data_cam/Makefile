# SPDX-License-Identifier: MIT
# Formal verification Makefile for pumice_wr_data_cam
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

# CI installs the pinned sv2v (v0.0.13) onto PATH (filelist-checks.yml). The
# dev machine keeps the same pinned binary at /mnt/data/tools/sv2v without
# putting it on PATH -- fall back to it so a bare `make formal-mc-common` works
# locally. Override with SV2V=<path> if neither applies.
SV2V      ?= $(shell command -v sv2v 2>/dev/null || echo /mnt/data/tools/sv2v)

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := wr_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_wr_data_cam.f
include $(REPO_ROOT)/make/formal_flat.mk

SHELL     := /bin/bash

.PHONY: prove prove_f1 prove_f2 cover all clean
all: prove cover
prove: prove_f1 prove_f2
prove_f1 prove_f2 cover: wr_flat.v
	sby -f wr_data_cam.sby $@
clean:
	rm -rf *_flat.v wr_flat.v wr_data_cam_prove wr_data_cam_cover \
	       wr_data_cam_prove_f1 wr_data_cam_prove_f2
