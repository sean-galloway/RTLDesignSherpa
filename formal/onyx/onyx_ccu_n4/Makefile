# SPDX-License-Identifier: MIT
# Formal verification Makefile for onyx_ccu at N_PORTS=4 (onyx TASK-001: the
# serializer and the gather proven safe at N = 2, 3, 4).  The harness is the
# N-generic formal/onyx/onyx_ccu_n3/formal_onyx_ccu_n.sv, shared with the
# other N; the N=2 unit is formal/onyx/onyx_ccu.
# Workflow: sv2v flattens the REAL RTL -> sby reads plain Verilog (plain prep).
# Geometry: as at N=2 except N_PORTS -- ADDR_WIDTH=8 (16 lines) /
# LINE_BYTES=16 / BUS_WIDTH=32 (four beats per line) / AXI_ID_WIDTH=3 /
# SLOTS=4 / SNOOP_INFLIGHT=2 / DEFER_AR=0 / SERIAL_MODE=0 (the reasons are in
# the harness header).  Regenerate the flat whenever the RTL changes.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

FLAT            := onyx_ccu_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/cache-ip/onyx-ace-ccu/rtl/filelists/onyx_ccu.f
FLAT_SV2V_FLAGS := --define=FORMAL --exclude=Assert
# the simulation-only contract checks (re-proven formally by the harness)
FLAT_PREP       := /pragma translate_off/,/pragma translate_on/d
FLAT_POST       := python3 $(REPO_ROOT)/formal/amber/specialize_params.py - /dev/stdout --param ADDR_WIDTH=8 --param LINE_BYTES=16 --param BUS_WIDTH=32 --param AXI_ID_WIDTH=3 --param AXI_USER_WIDTH=1 --param N_PORTS=4 --param SLOTS=4 --param SNOOP_INFLIGHT=2 --param DEFER_AR=0 --param SERIAL_MODE=0 --module onyx_ccu
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove prove-fast prove-book cover all clean

all: prove prove-fast prove-book cover

prove: onyx_ccu_flat.v
	sby -f onyx_ccu_n4.sby prove

prove-fast: onyx_ccu_flat.v
	sby -f onyx_ccu_n4.sby prove_fast

prove-book: onyx_ccu_flat.v
	sby -f onyx_ccu_n4.sby prove_book

cover: onyx_ccu_flat.v
	sby -f onyx_ccu_n4.sby cover

clean:
	rm -rf onyx_ccu_n4_prove onyx_ccu_n4_prove_fast onyx_ccu_n4_prove_book onyx_ccu_n4_cover
