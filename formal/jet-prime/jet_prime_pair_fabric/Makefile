# SPDX-License-Identifier: MIT
# Formal verification Makefile for jet_prime_pair_fabric (jet-prime TASK-001 step 4)
# Workflow: sv2v flattens the REAL RTL -> sby reads plain Verilog (plain prep).
#
# Closure: l1_pkg (the ACE request classes and the CRRESP bit map) + the reset
# macros + jet_prime_pair_fabric itself -- the fabric is self-contained RTL
# (no foreign module deps).  Both caches, both snoop responders and the
# shared memory are the harness's free environment under the documented
# contracts (formal_jet_prime_pair_fabric.sv, assumption inventory).
# Geometry: the tiny formal configuration ADDR_WIDTH=8 (16 lines) / LINE_BYTES=16 /
# BUS_WIDTH=32 (four beats per line) / AXI_ID_WIDTH=3 / FAB_SLOTS=4 /
# SNOOP_INFLIGHT=2 -- two slots per direction is enough for a same-line
# conflict to wait behind a live transaction while a distinct-line one runs
# beside it, and SNOOP_INFLIGHT=2 is the shipped value.
# Regenerate the flat file whenever the RTL changes.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := jet_prime_pair_fabric_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/cache-ip/jet-prime-mesi-l1/rtl/filelists/jet_prime_pair_fabric.f
# --define=FORMAL keeps the in-RTL formal blocks; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (vault/handbook/dv/formal.md).
FLAT_SV2V_FLAGS := --define=FORMAL --exclude=Assert
# The fabric's simulation-only contract checks sit between
# `pragma translate_off/on` comments; sv2v passes them through and this
# yosys build cannot parse the emitted form, so the prep strips them (the
# harness re-proves every one of them formally: AR/slot pairing, memory
# beat has a read outstanding, unique line per slot, CD only with a snoop
# outstanding, no pending-queue overflow).
FLAT_PREP       := /pragma translate_off/,/pragma translate_on/d
# specialize_params pins the tiny formal geometry AND deletes the parameter
# declarations, so the DUT is parameterless and yosys's expose applies
# (bind silently never fires in this yosys build -- amber Task 13 finding).
FLAT_POST       := python3 $(REPO_ROOT)/formal/amber/specialize_params.py - /dev/stdout --param ADDR_WIDTH=8 --param SETS=16 --param WAYS=2 --param LINE_BYTES=16 --param BUS_WIDTH=32 --param AXI_ID_WIDTH=3 --param AXI_USER_WIDTH=1 --param FAB_SLOTS=4 --param SNOOP_INFLIGHT=2 --module jet_prime_pair_fabric
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove prove-book cover all clean

all: prove prove-book cover

# the 25 local safety properties, BMC depth 24
prove: jet_prime_pair_fabric_flat.v
	sby -f jet_prime_pair_fabric.sby prove

# the three end-to-end bookkeeping properties, BMC depth 16 (see the .sby)
prove-book: jet_prime_pair_fabric_flat.v
	sby -f jet_prime_pair_fabric.sby prove_book

cover: jet_prime_pair_fabric_flat.v
	sby -f jet_prime_pair_fabric.sby cover

clean:
	rm -rf jet_prime_pair_fabric_prove jet_prime_pair_fabric_prove_book jet_prime_pair_fabric_cover
