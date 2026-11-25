# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# peregrine_core spliced properties (riscv-ip/peregrine-rv32im TASK-001
# stage 5): the predictor training rule, peregrine_core_props.svh, spliced
# before peregrine_core's endmodule in the flat (the RTL carries no
# assertions).
#
#     export PATH=/mnt/data/tools/oss-cad-suite/bin:/tmp/sv2v/sv2v-Linux:$PATH
#     make -C formal/peregrine/core_props prove
#     make -C formal/peregrine/core_props cover

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

# formal_flat.mk forces the *_ROOT variables it knows from REPO_ROOT;
# peregrine's is not among them, so it is forced here the same way.
export PEREGRINE_ROOT := $(REPO_ROOT)/projects/components/riscv-ip/peregrine-rv32im

FLAT             := peregrine_core_props_flat.v
FLAT_FILELIST    := $(PEREGRINE_ROOT)/rtl/filelists/top/peregrine_core.f
FLAT_SV2V_FLAGS  := --define=FORMAL --exclude=Assert
FLAT_SPLICE      := $(REPO_ROOT)/formal/peregrine/core_props/peregrine_core_props.svh
FLAT_SPLICE_INTO := peregrine_core.sv
include $(REPO_ROOT)/make/formal_flat.mk

# The flat is untracked and re-converted on every run (riscv-formal's
# reason: an RTL edit under an unchanged .f must reach it).
$(FLAT): FORCE
FORCE:

.PHONY: all prove cover clean FORCE

all: prove cover

prove: $(FLAT)
	sby -f peregrine_core_props.sby prove

cover: $(FLAT)
	sby -f peregrine_core_props.sby cover

clean: flat-clean
	rm -rf peregrine_core_props_prove peregrine_core_props_cover
