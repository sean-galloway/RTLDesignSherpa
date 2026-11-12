# SPDX-License-Identifier: MIT
# mc_bank_pick: equivalence of the resolved winner / stale-mask registers
# (memory-controllers MC-011, 2026-11-08) against the golden copy of the
# mux-resolved form -- every output, every cycle, free inputs.
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
REPO_ROOT ?= $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
FLAT            := bank_pick_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_bank_pick.f
include $(REPO_ROOT)/make/formal_flat.mk

# The golden copy (mc_bank_pick_gold.sv) flattened the same way from its own .f.
GOLD_FLAT := bank_pick_gold_flat.v
$(GOLD_FLAT): mc_bank_pick_gold.sv filelists/gold.f
	@mkdir -p $(FLAT_BUILD)
	$(FLATTEN) filelists/gold.f --absolute-paths --resolve-env | grep -vE '^[[:space:]]*(#|$$)' \
		| grep -E '^\+incdir\+|\.(sv|v|svh|vh)$$' > $(FLAT_BUILD)/gold.f
	$(SV2V) $$(grep '^+incdir+' $(FLAT_BUILD)/gold.f | sed 's/^+incdir+/-I/') \
		$$(grep -v '^+incdir+' $(FLAT_BUILD)/gold.f) > $@.tmp
	@mv $@.tmp $@

.PHONY: equiv equiv_n4 cover dual dual_cover all clean
all: equiv equiv_n4 cover dual dual_cover
equiv: $(FLAT) $(GOLD_FLAT)
	sby -f bank_pick.sby equiv
equiv_n4: $(FLAT) $(GOLD_FLAT)
	sby -f bank_pick.sby equiv_n4
cover: $(FLAT) $(GOLD_FLAT)
	sby -f bank_pick.sby cover
# the DUAL_ISSUE row lane's word invariants (MC-014), DUT alone at DUAL_ISSUE = 1
dual: $(FLAT) $(GOLD_FLAT)
	sby -f bank_pick.sby dual
dual_cover: $(FLAT) $(GOLD_FLAT)
	sby -f bank_pick.sby dual_cover
clean:
	rm -rf *_flat.v .flat_build bank_pick_equiv bank_pick_equiv_n4 bank_pick_cover bank_pick_dual bank_pick_dual_cover
