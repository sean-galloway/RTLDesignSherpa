# SPDX-License-Identifier: MIT
# Formal verification Makefile for monbus_arbiter
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
#
# Carries the three properties that used to be runtime assertions inside
# rtl/amba/ocelus/monbus_arbiter.sv (issue #112): grant one-hot, grant[grant_id],
# ready only to the granted client. See formal_monbus_arbiter.sv for the
# configuration choice (input skids off, so A3 is checked on a port).

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := monbus_arbiter_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/amba/filelists/monbus_arbiter.f
FLAT_SV2V_FLAGS := --define=FORMAL
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: monbus_arbiter_flat.v
	sby -f monbus_arbiter.sby prove

cover: monbus_arbiter_flat.v
	sby -f monbus_arbiter.sby cover

clean:
	rm -rf monbus_arbiter_flat.v monbus_arbiter_prove monbus_arbiter_cover
