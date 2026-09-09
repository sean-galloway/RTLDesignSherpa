# SPDX-License-Identifier: MIT
# Formal verification Makefile for wb4_master
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
# (same shape as formal/amba/apb4_monitor/Makefile; DEPS is the closure of
# wb4_master, leaves first, and the sv2v file list is derived from it).

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

PKGS := $(REPO_ROOT)/rtl/amba/wb4/wb4_pkg.sv

# RTL dependencies (transitive closure of wb4_master, leaves first)
DEPS := $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv

DUT := $(REPO_ROOT)/rtl/amba/wb4/wb4_master.sv

.PHONY: prove cover clean

prove: wb4_master_flat.v
	sby -f wb4_master.sby prove

cover: wb4_master_flat.v
	sby -f wb4_master.sby cover

# --define=FORMAL keeps the in-RTL properties; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (see vault/handbook/dv/formal.md).
wb4_master_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(DEPS) $(DUT) > $@
	@echo "asserts in flat: $$(grep -c 'assert' $@)"

clean:
	rm -rf *_flat.v *_prove *_cover
