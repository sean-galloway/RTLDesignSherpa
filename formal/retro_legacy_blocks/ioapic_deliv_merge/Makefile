# SPDX-License-Identifier: MIT
# Formal verification Makefile for ioapic_deliv_merge (retro_legacy_blocks)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
#
# DEPS is the transitive module closure of ioapic_deliv_merge, leaves first:
# the merge instantiates arbiter_round_robin, which instantiates
# arbiter_priority_encoder. The sv2v file list is DERIVED from $(DEPS) and
# $(DUT), so the flatten and the dependency list cannot drift apart.
#
# That drift is not hypothetical. An earlier version of this file crammed all
# three sources into DUT and omitted arbiter_priority_encoder, and yosys
# stopped with "Module `\arbiter_priority_encoder' referenced in module
# `\arbiter_round_robin' ... is not part of the design". The same omission also
# made a lint waiver read as non-load-bearing, because the arbiter never
# elaborated -- one mistake, two symptoms that looked unrelated.
#
# tools/gen_formal_deps.py regenerates this block elsewhere, but it cannot be
# used here: it builds its module map by walking $REPO/rtl only, so a DUT under
# projects/components/** is "unknown top" and it skips the directory. Its --all
# is likewise hardcoded to formal/amba. The DEPS *pattern* is not amba-only
# though -- formal/stream/axi_write_engine and formal/rapids/* use it with
# projects/-hosted DUTs, and this follows that shape.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

# No packages: the merge uses no package-typed ports.
PKGS :=

# RTL dependencies (transitive closure of ioapic_deliv_merge, leaves first)
DEPS := $(REPO_ROOT)/rtl/common/arbiter_priority_encoder.sv \
        $(REPO_ROOT)/rtl/common/arbiter_round_robin.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/retro_legacy_blocks/rtl/ioapic/ioapic_deliv_merge.sv

.PHONY: prove cover all clean

all: prove cover

prove: ioapic_deliv_merge_flat.v
	sby -f ioapic_deliv_merge.sby prove

cover: ioapic_deliv_merge_flat.v
	sby -f ioapic_deliv_merge.sby cover

ioapic_deliv_merge_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover ioapic_deliv_merge/
