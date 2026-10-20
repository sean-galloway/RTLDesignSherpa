# SPDX-License-Identifier: MIT
# Formal verification Makefile for stream_core
# Workflow: filelist closure -> one sed prep -> sv2v flattens -> sby reads plain Verilog
#
# SOURCES COME FROM THE FILELIST, NOT A HAND LIST (BUG-003, 2026-09-24).
# This Makefile used to hand-list 31 sources and rotted behind the monitor
# rework: it was missing monitor_trans_cam and ALL SIX axi_monitor_reporter_*
# sub-blocks, so `make prove` died at elaboration. stream_core.f says why in
# its own header -- "a consumer that hand-lists a component's files has to
# track that component's internal dependencies, and it silently rots when they
# change". So we resolve the filelist instead, and the rot cannot recur.
#
# This was the first formal Makefile to drive from a filelist (BUG-003). Since
# 2026-10-19 every formal flat does, through make/formal_flat.mk.
#
# The old `ocelus_pkg` sed workaround is GONE. Its premise -- "sv2v cannot
# handle the typedef re-export ambiguity" -- was re-tested against sv2v v0.0.13
# on the full 51-source closure INCLUDING ocelus_pkg.sv: RC=0, clean stderr.
# Seven sed-prepped monitor copies are no longer needed.
#
# ONE prep remains: sv2v does not honour `// synopsys translate_off`, so the
# hang-diagnostic $display in axi_write_engine survives into the flat and yosys
# cannot size its $time argument (AST_AUTOWIRE). Strip it for FORMAL ONLY --
# simulation reads the original source and still gets the prints.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := stream_core_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/dma-ip/stream/rtl/filelists/macro/stream_core.f
FLAT_PREP       := /synopsys translate_off/,/synopsys translate_on/d
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean

prove: stream_core_flat.v
	sby -f stream_core.sby prove

cover: stream_core_flat.v
	sby -f stream_core.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover $(FLAT_BUILD)
