# SPDX-License-Identifier: MIT
# Formal verification Makefile for apb_monitor
# Workflow: sv2v flattens SystemVerilog (packages) -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes

# Package files (order matters: dependencies first)
# NOTE: monitor_pkg.sv replaced with empty stub to avoid sv2v ambiguity
# from re-exported typedefs.  The sub-packages provide all needed types.
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba5_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_arbiter_pkg.sv \
        monitor_pkg_stub.sv

# RTL dependencies
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv

# Device under test
DUT := $(REPO_ROOT)/rtl/amba/apb/apb_monitor.sv

.PHONY: prove cover clean

prove: apb_monitor_flat.v
	sby -f apb_monitor.sby prove

cover: apb_monitor_flat.v
	sby -f apb_monitor.sby cover

apb_monitor_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
