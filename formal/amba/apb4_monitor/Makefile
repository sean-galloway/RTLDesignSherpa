# SPDX-License-Identifier: MIT
# Formal verification Makefile for apb4_monitor
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := apb4_monitor_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/amba/filelists/apb4_monitor.f
# ocelus_pkg re-exports its sub-packages' types, which trips sv2v's
# "ambiguous identifier"; the prep strips the import and the scope prefix.
FLAT_PREP       := s/import ocelus_pkg::\*;//g;s/ocelus_pkg:://g
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover clean

prove: apb4_monitor_flat.v
	sby -f apb4_monitor.sby prove

cover: apb4_monitor_flat.v
	sby -f apb4_monitor.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover
