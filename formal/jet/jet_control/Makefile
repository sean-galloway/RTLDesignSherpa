# SPDX-License-Identifier: MIT
# Formal verification Makefile for jet_control
# Workflow: sv2v flattens the REAL RTL -> sby reads plain Verilog (plain prep).
#
# Closure: jet_pkg (which closes l1_pkg) + jet_mshr + jet_wb_buffer +
# jet_rsp_seq + jet_control.  The three leaf blocks are real RTL in the
# wrapper (the control layer drives them; the proof is about the control
# decisions WITH the real files behind the handshake pins).  The tag/data
# arrays stay outside: the safety wrapper models the tag store abstractly
# (exact at 16x2), the liveness wrapper frees the tag reads (liveness
# quantifies over all tag behaviors).  l1_fill / l1_drain are rig-top
# integrations (jet_top), so the harness drives their handshake pins as
# free inputs under the documented engine-contract assumptions.
# Geometry: the tiny formal configuration SETS=16 / WAYS=2 / LINE_BYTES=64
# / BUS_WIDTH=64 / MSHR_COUNT=2 / VICTIM_DEPTH=2 (MSHR-full and set
# oversubscription are reachable exactly there -- MAS ch05/01).
# Regenerate the flat file whenever the RTL changes.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT closure's own filelists, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := jet_control_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_mshr.f \
                   $(REPO_ROOT)/projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_wb_buffer.f \
                   $(REPO_ROOT)/projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_rsp_seq.f \
                   $(REPO_ROOT)/projects/components/cache-ip/jet-mesi-l1/rtl/filelists/jet_control.f
# --define=FORMAL keeps the in-RTL formal blocks; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (vault/handbook/dv/formal.md).
FLAT_SV2V_FLAGS := --define=FORMAL --exclude=Assert
# The jet RTL's simulation-only contract checks sit between
# `pragma translate_off/on` comments (amber's control module carries none);
# sv2v passes them through and this yosys build cannot parse the emitted
# concurrent-assertion form, so the prep strips them (they are sim-only by
# construction; the wrapper re-proves the load-bearing ones formally).
FLAT_PREP       := /pragma translate_off/,/pragma translate_on/d
# specialize_params pins the tiny formal geometry AND deletes the parameter
# declarations, so the DUT is parameterless and yosys's expose applies
# (bind silently never fires in this yosys build -- amber Task 13 finding).
FLAT_POST       := python3 $(REPO_ROOT)/formal/amber/specialize_params.py - /dev/stdout --param ADDR_WIDTH=32 --param SETS=16 --param WAYS=2 --param LINE_BYTES=64 --param BUS_WIDTH=64 --param MSHR_COUNT=2 --param VICTIM_DEPTH=2 --module jet_control
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove prove-live cover all clean

all: prove prove-live cover

prove: jet_control_flat.v
	sby -f jet_control.sby prove

# bounded-liveness (the J5/J6 deadlock corner) -- free-tag wrapper, BMC
prove-live: jet_control_flat.v
	sby -f jet_control_live.sby prove

cover: jet_control_flat.v
	sby -f jet_control.sby cover
	sby -f jet_control_live.sby cover

clean:
	rm -rf jet_control_prove jet_control_cover jet_control_live_prove jet_control_live_cover
