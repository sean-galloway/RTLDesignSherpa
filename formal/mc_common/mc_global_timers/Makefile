# SPDX-License-Identifier: MIT
# Formal verification Makefile for global_timers (pumice)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT ?= $(shell git rev-parse --show-toplevel)

SV2V      ?= sv2v

# The flat's source list is the DUT's own filelist, flattened by
# bin/flatten_filelist.py (make/formal_flat.mk) -- never hand-listed.
FLAT            := global_timers_flat.v
FLAT_FILELIST   := $(REPO_ROOT)/projects/components/mem-ctrl-ip/common-ip/rtl/filelists/fub/mc_global_timers.f
include $(REPO_ROOT)/make/formal_flat.mk

# The golden copy (mc_global_timers_gold.sv, the serial slot search as
# committed at 821b5c164) for the equiv task, flattened the same way from its
# own .f.
GOLD_FLAT := global_timers_gold_flat.v
$(GOLD_FLAT): mc_global_timers_gold.sv filelists/gold.f
	@mkdir -p $(FLAT_BUILD)
	$(FLATTEN) filelists/gold.f --absolute-paths --resolve-env | grep -vE '^[[:space:]]*(#|$$)' \
		| grep -E '^\+incdir\+|\.(sv|v|svh|vh)$$' > $(FLAT_BUILD)/gold.f
	$(SV2V) $$(grep '^+incdir+' $(FLAT_BUILD)/gold.f | sed 's/^+incdir+/-I/') \
		$$(grep -v '^+incdir+' $(FLAT_BUILD)/gold.f) > $@.tmp
	@mv $@.tmp $@

.PHONY: prove cover equiv all clean

all: prove cover equiv

prove: global_timers_flat.v
	sby -f global_timers.sby prove

cover: global_timers_flat.v
	sby -f global_timers.sby cover

equiv: global_timers_flat.v $(GOLD_FLAT)
	sby -f global_timers.sby equiv

clean:
	rm -rf *_flat.v .flat_build global_timers_prove global_timers_cover global_timers_equiv
