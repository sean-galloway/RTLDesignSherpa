# SPDX-License-Identifier: MIT
# Formal verification Makefile for scoria_addr_mapper
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
SCORIA    := $(REPO_ROOT)/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(SCORIA)/rtl/includes
PKGS := $(SCORIA)/rtl/includes/scoria_pkg.sv
DUT  := $(SCORIA)/rtl/fub/scoria_addr_mapper.sv

.PHONY: prove cover all clean

all: prove cover

prove: addr_mapper_flat.v
	sby -f scoria_addr_mapper.sby prove

cover: addr_mapper_flat.v
	sby -f scoria_addr_mapper.sby cover

addr_mapper_flat.v: $(DUT) $(PKGS)
	$(SV2V) $(INC) $(PKGS) $(DUT) > $@

clean:
	rm -rf *_flat.v addr_mapper_prove addr_mapper_cover
