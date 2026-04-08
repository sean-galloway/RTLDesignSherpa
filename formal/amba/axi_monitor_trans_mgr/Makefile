# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi_monitor_trans_mgr
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes

# Package files (order matters: dependencies first)
# Note: monitor_pkg excluded -- it re-exports types from monitor_amba4_pkg
# which causes sv2v "ambiguous identifier" errors. The DUT's
# `import monitor_pkg::*;` is stripped via sed before sv2v runs.
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv

# RTL dependencies (pure logic - no submodule instantiations)
DEPS :=

# Device under test
DUT := $(REPO_ROOT)/rtl/amba/shared/axi_monitor_trans_mgr.sv

.PHONY: prove cover clean

prove: axi_monitor_trans_mgr_flat.v
	sby -f axi_monitor_trans_mgr.sby prove

cover: axi_monitor_trans_mgr_flat.v
	sby -f axi_monitor_trans_mgr.sby cover

axi_monitor_trans_mgr_flat.v: $(DUT) $(PKGS)
	sed 's/import monitor_pkg::\*;//g' $(DUT) > /tmp/axi_monitor_trans_mgr_nopkg.sv
	$(SV2V) $(INC) $(PKGS) /tmp/axi_monitor_trans_mgr_nopkg.sv > $@

clean:
	rm -rf *_flat.v *_prove *_cover
