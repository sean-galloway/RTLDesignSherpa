# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi4_dwidth_converter_rd
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes

# Package files (none needed - uses reset_defs.svh only)
PKGS :=

# RTL dependencies (gaxi_skid_buffer used for timing closure; the data-width
# primitives are instantiated by the DUT and must be in the flat or prep fails)
DEPS := $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv \
        $(REPO_ROOT)/projects/components/utility-ip/converters/rtl/axi_data_upsize.sv \
        $(REPO_ROOT)/projects/components/utility-ip/converters/rtl/axi_data_dnsize.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/utility-ip/converters/rtl/axi4_dwidth_converter_rd.sv

.PHONY: prove cover clean

prove: axi4_dwidth_converter_rd_flat.v
	sby -f axi4_dwidth_converter_rd.sby prove

cover: axi4_dwidth_converter_rd_flat.v
	sby -f axi4_dwidth_converter_rd.sby cover

axi4_dwidth_converter_rd_flat.v: $(DUT) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
