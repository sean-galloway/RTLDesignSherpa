# SPDX-License-Identifier: MIT
# Formal verification Makefile for ioapic_deliv_merge (retro_legacy_blocks)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes
# The merge instantiates arbiter_round_robin, which in turn instantiates
# arbiter_priority_encoder. sv2v needs the WHOLE closure or yosys stops with
# "Module `\arbiter_priority_encoder' ... is not part of the design" -- which is
# exactly what an earlier two-file version of this list produced.
#
# The authoritative dependency list is rtl/common/filelists/arbiter_round_robin.f
# and this must track it. It is hand-listed because every formal Makefile in
# this repo hand-lists its DUT; none expands a filelist. If the arbiter grows a
# dependency, it has to be added here too.
DUT := $(REPO_ROOT)/rtl/common/arbiter_priority_encoder.sv \
       $(REPO_ROOT)/rtl/common/arbiter_round_robin.sv \
       $(REPO_ROOT)/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_deliv_merge.sv

.PHONY: prove cover all clean

all: prove cover

prove: ioapic_deliv_merge_flat.v
	sby -f ioapic_deliv_merge.sby prove

cover: ioapic_deliv_merge_flat.v
	sby -f ioapic_deliv_merge.sby cover

ioapic_deliv_merge_flat.v: $(DUT)
	$(SV2V) $(INC) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover ioapic_deliv_merge/
