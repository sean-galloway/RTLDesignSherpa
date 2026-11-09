# SPDX-License-Identifier: MIT
# Formal verification Makefile for bank_timer (pumice)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
#
# The flatten is not optional here: yosys's Verilog frontend cannot parse
# pumice_pkg.sv (a multi-line `return` in a package function, pumice_pkg.sv:131),
# so reading the .sv directly fails before any proof runs.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := bank_timer_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_bank_timer.f
include $(REPO_ROOT)/make/formal_flat.mk

# The golden copy (mc_bank_timer_gold.sv, the live-compare form as committed at
# 821b5c164) for the equiv tasks, flattened the same way from its own .f.
GOLD_FLAT := bank_timer_gold_flat.v
$(GOLD_FLAT): mc_bank_timer_gold.sv filelists/gold.f
	@mkdir -p $(FLAT_BUILD)
	$(FLATTEN) filelists/gold.f --absolute-paths --resolve-env | grep -vE '^[[:space:]]*(#|$$)' \
		| grep -E '^\+incdir\+|\.(sv|v|svh|vh)$$' > $(FLAT_BUILD)/gold.f
	$(SV2V) $$(grep '^+incdir+' $(FLAT_BUILD)/gold.f | sed 's/^+incdir+/-I/') \
		$$(grep -v '^+incdir+' $(FLAT_BUILD)/gold.f) > $@.tmp
	@mv $@.tmp $@

.PHONY: prove cover equiv equiv_live all clean

all: prove cover equiv equiv_live

equiv: bank_timer_flat.v $(GOLD_FLAT)
	sby -f bank_timer.sby equiv

equiv_live: bank_timer_flat.v $(GOLD_FLAT)
	sby -f bank_timer.sby equiv_live

prove: bank_timer_flat.v
	sby -f bank_timer.sby prove

cover: bank_timer_flat.v
	sby -f bank_timer.sby cover

clean:
	rm -rf *_flat.v *_prove *_cover *_equiv *_equiv_live
