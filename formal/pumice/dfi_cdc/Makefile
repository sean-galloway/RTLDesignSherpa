# SPDX-License-Identifier: MIT
# Formal verification Makefile for pumice_dfi_cdc.
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# Deps follow rtl/filelists/fub/pumice_dfi_cdc.f, which is the authority.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
PUMICE    := $(REPO_ROOT)/projects/components/memory-controllers/pumice-ddr2-lpddr2

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(PUMICE)/rtl/includes
PKGS := $(PUMICE)/rtl/includes/pumice_pkg.sv
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
DUT  := $(PUMICE)/rtl/fub/pumice_dfi_cdc.sv

.PHONY: prove cover all clean
all: prove cover
prove: cdc_flat.v
	sby -f dfi_cdc.sby prove
cover: cdc_flat.v
	sby -f dfi_cdc.sby cover
cdc_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@
clean:
	rm -rf *_flat.v cdc_flat.v dfi_cdc_prove dfi_cdc_cover
