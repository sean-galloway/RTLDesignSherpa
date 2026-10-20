# SPDX-License-Identifier: MIT
# Formal verification Makefile for pumice_rd_cmd_cam
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := cam_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/amba/filelists/gaxi_fifo_sync.f \
                   $(REPO_ROOT)/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_rd_cmd_cam.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean
all: prove cover
prove: cam_flat.v
	sby -f rd_cmd_cam.sby prove
cover: cam_flat.v
	sby -f rd_cmd_cam.sby cover
clean:
	rm -rf *_flat.v cam_flat.v rd_cmd_cam_prove rd_cmd_cam_cover
