# SPDX-License-Identifier: MIT
# Formal verification Makefile for wb4_monitor
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
# (same shape as formal/amba/apb4_monitor/Makefile; DEPS is the closure of
# wb4_monitor, leaves first, and the sv2v file list is derived from it).

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_wb4_pkg.sv \
        $(REPO_ROOT)/rtl/amba/wb4/wb4_pkg.sv

# RTL dependencies (transitive closure of wb4_monitor, leaves first)
DEPS := $(REPO_ROOT)/rtl/amba/monitor/apb_monitor_addr_check.sv \
        $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv

DUT := $(REPO_ROOT)/rtl/amba/wb4/wb4_monitor.sv

.PHONY: prove cover all clean

all: prove cover

prove: wb4_monitor_flat.v
	sby -f wb4_monitor.sby prove

cover: wb4_monitor_flat.v
	sby -f wb4_monitor.sby cover

# --define=FORMAL keeps the in-RTL properties; --exclude=Assert keeps sv2v
# from deleting the immediate assertions (see vault/handbook/dv/formal.md).
wb4_monitor_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(DEPS) $(DUT) > $@
	@echo "asserts in flat: $$(grep -c 'assert' $@)"

clean:
	rm -rf *_flat.v *_prove *_cover
