# SPDX-License-Identifier: MIT
# Formal verification Makefile for axil4_to_wb4_core
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog (the
# core imports wb4_pkg and uses the reset_defs macros, which the plain
# `read -sv` flow of the other converters harnesses does not need).

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

PKGS := $(REPO_ROOT)/rtl/amba/wb4/wb4_pkg.sv

# RTL dependencies (transitive closure, leaves first)
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv

DUT := $(REPO_ROOT)/projects/components/converters/rtl/axil4_to_wb4_core.sv

.PHONY: prove cover all clean

all: prove cover

prove: axil4_to_wb4_core_flat.v
	sby -f axil4_to_wb4_core.sby prove

cover: axil4_to_wb4_core_flat.v
	sby -f axil4_to_wb4_core.sby cover

# --define=FORMAL keeps the in-RTL properties; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (see vault/handbook/dv/formal.md).
axil4_to_wb4_core_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(DEPS) $(DUT) > $@
	@echo "asserts in flat: $$(grep -c 'assert' $@)"

clean:
	rm -rf *_flat.v *_prove *_cover
