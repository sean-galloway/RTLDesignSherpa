# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi4_dwidth_converter_rd
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes

# Package files (none needed - uses reset_defs.svh only)
PKGS :=

# RTL dependencies (gaxi_skid_buffer used for timing closure)
DEPS := $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/converters/rtl/axi4_dwidth_converter_rd.sv

.PHONY: prove cover clean

prove: axi4_dwidth_converter_rd_flat.v
	sby -f axi4_dwidth_converter_rd.sby prove

cover: axi4_dwidth_converter_rd_flat.v
	sby -f axi4_dwidth_converter_rd.sby cover

axi4_dwidth_converter_rd_flat.v: $(DUT) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
