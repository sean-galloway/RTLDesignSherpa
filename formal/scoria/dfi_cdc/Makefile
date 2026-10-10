# SPDX-License-Identifier: MIT
# Formal verification Makefile for scoria_dfi_cdc.
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# Deps follow rtl/filelists/fub/scoria_dfi_cdc.f, which is the authority.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
SCORIA    := $(REPO_ROOT)/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(SCORIA)/rtl/includes
PKGS := $(SCORIA)/rtl/includes/scoria_pkg.sv
# Closure taken from rtl/cdc/filelists/cdc_fifo_bb.f, which is the authority --
# hand-assembling it missed gray2bin and counter_bingray and the build failed
# with "Module `\gray2bin' ... is not part of the design".
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/cdc/glitch_free_n_dff_arn.sv \
        $(REPO_ROOT)/rtl/common/find_first_set.sv \
        $(REPO_ROOT)/rtl/common/find_last_set.sv \
        $(REPO_ROOT)/rtl/common/leading_one_trailing_one.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/cdc/gray2bin.sv \
        $(REPO_ROOT)/rtl/cdc/bin2gray.sv \
        $(REPO_ROOT)/rtl/cdc/counter_bingray.sv \
        $(REPO_ROOT)/rtl/cdc/counter_johnson.sv \
        $(REPO_ROOT)/rtl/cdc/johnson2bin.sv \
        $(REPO_ROOT)/rtl/cdc/gaxi_fifo_async.sv
DUT  := $(SCORIA)/rtl/fub/scoria_dfi_cdc.sv

.PHONY: prove cover all clean
all: prove cover
prove: cdc_flat.v
	sby -f scoria_dfi_cdc.sby prove
cover: cdc_flat.v
	sby -f scoria_dfi_cdc.sby cover
cdc_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@
clean:
	rm -rf *_flat.v cdc_flat.v dfi_cdc_prove dfi_cdc_cover

# tooling TASK-026: regenerate-and-diff self-detection for the committed flat.
# House pattern from formal/common/counter_freq_invariant; consumed by
# bin/formal_status.py --check-flats (mechanism a) and the pre-commit gate.
# Comparison squeezes whitespace, matching the token normalization the
# checker uses (committed flats may be post-formatter).
.PHONY: check-flat .check_flat_tmp
check-flat: .check_flat_tmp
	@if [ "$$(tr -s '[:space:]' ' ' < .check_flat_tmp)" = "$$(tr -s '[:space:]' ' ' < cdc_flat.v)" ]; then \
		rm -f .check_flat_tmp; \
		echo "flat file is current"; \
	else \
		rm -f .check_flat_tmp; \
		echo "STALE: cdc_flat.v does not match the RTL."; \
		echo "Regenerate with: make cdc_flat.v"; \
		exit 1; \
	fi

.check_flat_tmp: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@