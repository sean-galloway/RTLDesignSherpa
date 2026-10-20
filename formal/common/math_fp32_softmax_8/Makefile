# SPDX-License-Identifier: MIT
# Formal verification Makefile for math_fp32_softmax_8
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
#
# This task was DEFERRED with the note "Yosys does not support unpacked array
# ports". That is still true of yosys's own frontend (verified 2026-09-11),
# but option 2 of that note -- flatten the array ports into packed vectors --
# is exactly what sv2v does, and sv2v is already the repo's formal front end.
# The harness reads the packed form. sv2v puts element 0 at the MSB end, so
# element i is bits [W*(7-i) +: W] (measured 2026-09-11).

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := math_fp32_softmax_8_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/math/filelists/math_fp32_softmax_8.f
# --define=FORMAL keeps the in-RTL formal blocks; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (vault/handbook/dv/formal.md).
FLAT_SV2V_FLAGS := --define=FORMAL --exclude=Assert
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: math_fp32_softmax_8_flat.v
	sby -f math_fp32_softmax_8.sby prove

cover: math_fp32_softmax_8_flat.v
	sby -f math_fp32_softmax_8.sby cover

clean:
	rm -rf math_fp32_softmax_8_flat.v math_fp32_softmax_8_prove math_fp32_softmax_8_cover
