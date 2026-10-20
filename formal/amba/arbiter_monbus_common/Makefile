# SPDX-License-Identifier: MIT
# Formal verification Makefile for arbiter_monbus_common
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
#
# THIS TASK USED TO PROVE A FORK. The directory held arbiter_monbus_common_formal.sv --
# a hand-copied variant of the RTL, 287 lines divergent from
# rtl/amba/ocelus/arbiter_monbus_common.sv -- because yosys's own SystemVerilog
# frontend cannot resolve package-typed ports (it DROPS the port, then reports
# it as missing). A proof about a copy proves nothing about the design, and
# this one could not run either way.
#
# sv2v resolves the package types, so the real RTL goes in and the fork is
# gone. No --exclude=Assert: these modules carry no `ifdef FORMAL properties,
# only ELABORATION asserts, and keeping those leaves `assert (...) else begin
# ... end` in the output, which yosys cannot parse.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := arbiter_monbus_common_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/amba/filelists/arbiter_monbus_common.f
FLAT_SV2V_FLAGS := --define=FORMAL
# ocelus_pkg re-exports its sub-packages' types, which trips sv2v's
# "ambiguous identifier"; the prep strips the import and the scope prefix.
FLAT_PREP       := s/import ocelus_pkg::\*;//g;s/ocelus_pkg:://g
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: arbiter_monbus_common_flat.v
	sby -f arbiter_monbus_common.sby prove

cover: arbiter_monbus_common_flat.v
	sby -f arbiter_monbus_common.sby cover

clean:
	rm -rf arbiter_monbus_common_flat.v arbiter_monbus_common_prove arbiter_monbus_common_cover
