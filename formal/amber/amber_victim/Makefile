# SPDX-License-Identifier: MIT
# Formal verification Makefile for l1_victim
# Workflow: sv2v flattens the REAL RTL -> sby reads plain Verilog (plain prep).
#
# Geometry: the tiny formal configuration SETS=16 / LINE_BYTES=64 / BUS_WIDTH=64
# (the register is geometry-parameterized only by the line width; SETS is a
# bound contract).
# Regenerate the flat file whenever the RTL changes.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := amber_victim_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/cache-ip/common-ip/rtl/filelists/l1_victim.f
# --define=FORMAL keeps the in-RTL formal blocks; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (vault/handbook/dv/formal.md).
FLAT_SV2V_FLAGS := --define=FORMAL --exclude=Assert
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: amber_victim_flat.v
	sby -f amber_victim.sby prove

cover: amber_victim_flat.v
	sby -f amber_victim.sby cover

clean:
	rm -rf amber_victim_prove amber_victim_cover
