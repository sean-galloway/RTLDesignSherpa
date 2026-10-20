# SPDX-License-Identifier: MIT
# Formal verification Makefile for l1_snoop_resp
# Workflow: sv2v flattens the REAL RTL -> sby reads plain Verilog (plain prep).
#
# Closure: l1_pkg + gaxi_skid_buffer + axi4ace_snoop_slave (the transport)
# + l1_snoop_resp. The proof is about the shipped responder including its
# skid-buffered ACE transport, not a fork.
# Regenerate the flat file whenever the RTL changes.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := amber_snoop_resp_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/cache-ip/common-ip/rtl/filelists/l1_snoop_resp.f
# --define=FORMAL keeps the in-RTL formal blocks; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (vault/handbook/dv/formal.md).
FLAT_SV2V_FLAGS := --define=FORMAL --exclude=Assert
# specialize_params pins the tiny formal geometry AND deletes the parameter
# declarations, so the DUT is parameterless and yosys's expose applies
# (bind silently never fires in this yosys build).
FLAT_POST       := python3 ../specialize_params.py - /dev/stdout --param ADDR_WIDTH=32 --param DATA_WIDTH=64 --param LINE_BYTES=64 --module l1_snoop_resp
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: amber_snoop_resp_flat.v
	sby -f amber_snoop_resp.sby prove

cover: amber_snoop_resp_flat.v
	sby -f amber_snoop_resp.sby cover

clean:
	rm -rf amber_snoop_resp_prove amber_snoop_resp_cover
