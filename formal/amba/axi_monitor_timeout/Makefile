# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi_monitor_timeout
# Workflow: sv2v flattens SystemVerilog (packages) -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes

# Package files (order matters: dependencies first)
# NOTE: monitor_pkg.sv replaced with empty stub to avoid sv2v ambiguity
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        monitor_pkg_stub.sv

# Device under test
DUT := $(REPO_ROOT)/rtl/amba/shared/axi_monitor_timeout.sv

.PHONY: prove cover clean

prove: axi_monitor_timeout_flat.v
	sby -f axi_monitor_timeout.sby prove

cover: axi_monitor_timeout_flat.v
	sby -f axi_monitor_timeout.sby cover

axi_monitor_timeout_flat.v: $(DUT) $(PKGS)
	sed 's/import monitor_pkg::\*;//g' $(DUT) > /tmp/axi_monitor_timeout_stripped.sv
	$(SV2V) $(INC) $(PKGS) /tmp/axi_monitor_timeout_stripped.sv > $@
	rm -f /tmp/axi_monitor_timeout_stripped.sv

clean:
	rm -rf *_flat.v *_prove *_cover
