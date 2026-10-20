# SPDX-License-Identifier: MIT
# Formal verification Makefile for pumice_dfi_cdc.
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

# CI installs the pinned sv2v (v0.0.13) onto PATH (filelist-checks.yml). The
# dev machine keeps the same pinned binary at /mnt/data/tools/sv2v without
# putting it on PATH -- fall back to it so a bare `make formal-mc-common` works
# locally. Override with SV2V=<path> if neither applies.
SV2V      ?= $(shell command -v sv2v 2>/dev/null || echo /mnt/data/tools/sv2v)

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := cdc_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/cdc/filelists/bin2gray.f \
                   $(REPO_ROOT)/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_dfi_cdc.f
# The wrapper needs the block's INTERNAL pairing/edge nets. yosys does not
# resolve dotted refs from the wrapper into the DUT -- they elaborate as
# implicit wires, which formal treats as FREE INPUTS -- so inject_probes.py
# adds probe output ports wired to those nets and audits every hookup.
FLAT_POST       := python3 inject_probes.py /dev/stdin /dev/stdout
include $(REPO_ROOT)/make/formal_flat.mk

SHELL     := /bin/bash

.PHONY: prove cover all clean
all: prove cover
prove: cdc_flat.v
	sby -f dfi_cdc.sby prove
cover: cdc_flat.v
	sby -f dfi_cdc.sby cover
clean:
	rm -rf *_flat.v cdc_flat.v cdc_sv2v.v dfi_cdc_prove dfi_cdc_cover
