# SPDX-License-Identifier: MIT
# Formal verification Makefile for rtc_config_regs (retro_legacy_blocks/rtc)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
#
# The DEPS order matters: the package first, then the bridge and the generated
# register block, then the DUT. peakrdl_to_cmdrsp is IN the closure on purpose
# -- the two-cycle regblk_req hold both proved properties turn on lives there,
# so modelling it instead of including it would prove the model, not the design.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

RLB := $(REPO_ROOT)/projects/components/retro_legacy_blocks/rtl/rtc

DEPS := $(RLB)/rtc_regs_pkg.sv \
        $(REPO_ROOT)/projects/components/converters/rtl/peakrdl_to_cmdrsp.sv \
        $(RLB)/rtc_regs.sv

DUT := $(RLB)/rtc_config_regs.sv

.PHONY: prove cover all clean

all: prove cover

prove: rtc_config_regs_flat.v
	sby -f rtc_config_regs.sby prove

cover: rtc_config_regs_flat.v
	sby -f rtc_config_regs.sby cover

rtc_config_regs_flat.v: $(DUT) $(DEPS)
	$(SV2V) $(INC) $(DEPS) $(DUT) > $@

clean:
	# sby also creates a bare <top>/ directory when prep -top names the DUT,
	# which *_prove/*_cover does not match and .gitignore does not cover.
	rm -rf *_flat.v *_prove *_cover rtc_config_regs/
