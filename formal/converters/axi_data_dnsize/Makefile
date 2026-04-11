# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi_data_dnsize
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes

# Package files (none needed)
PKGS :=

# RTL dependencies (none -- standalone module)
DEPS :=

# Device under test
DUT := $(REPO_ROOT)/projects/components/converters/rtl/axi_data_dnsize.sv

.PHONY: prove cover all clean

all: prove cover

prove: axi_data_dnsize_flat.v
	sby -f axi_data_dnsize.sby prove

cover: axi_data_dnsize_flat.v
	sby -f axi_data_dnsize.sby cover

axi_data_dnsize_flat.v: $(DUT) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
