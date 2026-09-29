# SPDX-License-Identifier: MIT
# Formal verification Makefile for addr_mapper (pumice)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
PUMICE    := $(REPO_ROOT)/projects/components/memory-controllers/pumice-ddr2-lpddr2

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(PUMICE)/rtl/includes
PKGS := $(PUMICE)/rtl/includes/pumice_pkg.sv
DUT  := $(PUMICE)/rtl/fub/addr_mapper.sv

.PHONY: prove cover all clean

all: prove cover

prove: addr_mapper_flat.v
	sby -f addr_mapper.sby prove

cover: addr_mapper_flat.v
	sby -f addr_mapper.sby cover

addr_mapper_flat.v: $(DUT) $(PKGS)
	$(SV2V) $(INC) $(PKGS) $(DUT) > $@

clean:
	rm -rf *_flat.v addr_mapper_prove addr_mapper_cover
