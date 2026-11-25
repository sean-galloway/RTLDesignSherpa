# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# peregrine_top properties (riscv-ip/peregrine-rv32im TASK-001 stage 5):
# the D-side wrapper contract, peregrine_top_props.svh, spliced before
# peregrine_top's endmodule in the flat (the RTL carries no assertions), and
# the fetch property in the harness.  amber's filelist is excluded: the
# harness supplies an amber_top stub with amber's CPU-port contract.
#
#     export PATH=/mnt/data/tools/oss-cad-suite/bin:/tmp/sv2v/sv2v-Linux:$PATH
#     make -C formal/peregrine/top_props prove
#     make -C formal/peregrine/top_props cover

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

# formal_flat.mk forces the *_ROOT variables it knows from REPO_ROOT;
# peregrine's is not among them, so it is forced here the same way.
export PEREGRINE_ROOT := $(REPO_ROOT)/projects/components/riscv-ip/peregrine-rv32im

FLAT             := peregrine_top_props_flat.v
FLAT_FILELIST    := $(PEREGRINE_ROOT)/rtl/filelists/top/peregrine_top.f
FLAT_EXCLUDE     := amber_top
FLAT_SV2V_FLAGS  := --define=FORMAL --exclude=Assert
FLAT_SPLICE      := $(REPO_ROOT)/formal/peregrine/top_props/peregrine_top_props.svh
FLAT_SPLICE_INTO := peregrine_top.sv
include $(REPO_ROOT)/make/formal_flat.mk

# The flat is untracked and re-converted on every run (riscv-formal's
# reason: an RTL edit under an unchanged .f must reach it).
$(FLAT): FORCE
FORCE:

.PHONY: all prove cover clean FORCE

all: prove cover

prove: $(FLAT)
	sby -f peregrine_top_props.sby prove

cover: $(FLAT)
	sby -f peregrine_top_props.sby cover

clean: flat-clean
	rm -rf peregrine_top_props_prove peregrine_top_props_cover
