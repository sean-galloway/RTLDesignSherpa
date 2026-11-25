# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# peregrine_mdu against the M-extension reference function (riscv-ip/
# peregrine-rv32im TASK-001 stage 5, PRD §5 targeted formal).
#
#     export PATH=/mnt/data/tools/oss-cad-suite/bin:/tmp/sv2v/sv2v-Linux:$PATH
#     make -C formal/peregrine/mdu_ref prove     # every operation
#     make -C formal/peregrine/mdu_ref <op>      # one: mul mulh ... remu
#     make -C formal/peregrine/mdu_ref cover

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

export PEREGRINE_ROOT := $(REPO_ROOT)/projects/components/riscv-ip/peregrine-rv32im

FLAT          := peregrine_mdu_flat.v
FLAT_FILELIST := $(PEREGRINE_ROOT)/rtl/filelists/fub/peregrine_mdu.f
include $(REPO_ROOT)/make/formal_flat.mk

$(FLAT): FORCE
FORCE:

OPS := mul mulh mulhsu mulhu div divu rem remu

.PHONY: all prove cover clean FORCE $(OPS)

all: prove cover

prove: $(OPS)

$(OPS): $(FLAT)
	sby -f peregrine_mdu_ref.sby $@

cover: $(FLAT)
	sby -f peregrine_mdu_ref.sby cover
	sby -f peregrine_mdu_ref.sby cover_mul

clean: flat-clean
	rm -rf $(addprefix peregrine_mdu_ref_,$(OPS) cover cover_mul)
