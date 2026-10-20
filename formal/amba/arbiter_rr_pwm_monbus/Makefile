# SPDX-License-Identifier: MIT
# Formal verification Makefile for arbiter_rr_pwm_monbus
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
#
# THIS TASK USED TO PROVE A FORK. The directory held
# arbiter_rr_pwm_monbus_formal.sv -- a hand-copied variant of the RTL, 251
# lines divergent from rtl/amba/ocelus/arbiter_rr_pwm_monbus.sv -- plus a
# monitor_pkg_stub.sv, because yosys's own SystemVerilog frontend cannot
# resolve package-typed ports (it DROPS the port and then reports it as
# missing). A proof about a copy proves nothing about the design, and this
# one could not run either way.
#
# sv2v resolves the package types, so the real RTL and the real packages go
# in and the fork is gone.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := arbiter_rr_pwm_monbus_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/rtl/amba/filelists/arbiter_rr_pwm_monbus.f
FLAT_SV2V_FLAGS := --define=FORMAL
# ocelus_pkg re-exports its sub-packages' types, which trips sv2v's
# "ambiguous identifier"; the prep strips the import and the scope prefix.
FLAT_PREP       := s/import ocelus_pkg::\*;//g;s/ocelus_pkg:://g
include $(REPO_ROOT)/make/formal_flat.mk

.PHONY: prove cover all clean

all: prove cover

prove: arbiter_rr_pwm_monbus_flat.v
	sby -f arbiter_rr_pwm_monbus.sby prove

cover: arbiter_rr_pwm_monbus_flat.v
	sby -f arbiter_rr_pwm_monbus.sby cover

clean:
	rm -rf arbiter_rr_pwm_monbus_flat.v arbiter_rr_pwm_monbus_prove arbiter_rr_pwm_monbus_cover
