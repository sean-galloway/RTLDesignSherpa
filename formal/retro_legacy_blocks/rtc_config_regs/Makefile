# SPDX-License-Identifier: MIT
# Formal verification Makefile for rtc_config_regs (retro_legacy_blocks/rtc)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
#
# peakrdl_to_cmdrsp is IN the closure (rtc_config_regs.f) on purpose
# -- the two-cycle regblk_req hold both proved properties turn on lives there,
# so modelling it instead of including it would prove the model, not the design.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := rtc_config_regs_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/legacy-ip/retro_legacy_blocks/rtl/rtc/filelists/rtc_config_regs.f
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: rtc_config_regs_flat.v
	sby -f rtc_config_regs.sby prove

cover: rtc_config_regs_flat.v
	sby -f rtc_config_regs.sby cover

clean:
	# sby also creates a bare <top>/ directory when prep -top names the DUT,
	# which *_prove/*_cover does not match and .gitignore does not cover.
	rm -rf *_flat.v *_prove *_cover rtc_config_regs/
