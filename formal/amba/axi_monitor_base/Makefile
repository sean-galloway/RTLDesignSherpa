# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi_monitor_base
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes

# Package files (order matters: dependencies first)
# Note: monitor_pkg excluded -- it re-exports types from sub-packages
# which causes sv2v "ambiguous identifier" errors.
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv

# RTL dependencies (all submodules of axi_monitor_base)
DEPS := $(REPO_ROOT)/rtl/amba/shared/axi_monitor_trans_mgr.sv \
        $(REPO_ROOT)/rtl/amba/shared/axi_monitor_timer.sv \
        $(REPO_ROOT)/rtl/common/counter_freq_invariant.sv \
        $(REPO_ROOT)/rtl/common/counter_load_clear.sv \
        $(REPO_ROOT)/rtl/amba/shared/axi_monitor_timeout.sv \
        $(REPO_ROOT)/rtl/amba/shared/axi_monitor_reporter.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv

# Device under test
DUT := $(REPO_ROOT)/rtl/amba/shared/axi_monitor_base.sv

TMPDIR := /tmp/formal_axi_monitor_base

.PHONY: prove cover clean

prove: axi_monitor_base_flat.v
	sby -f axi_monitor_base.sby prove

cover: axi_monitor_base_flat.v
	sby -f axi_monitor_base.sby cover

# Strip `import monitor_pkg::*;` from all SV files to avoid sv2v ambiguity,
# then flatten everything into a single Verilog file.
axi_monitor_base_flat.v: $(DUT) $(PKGS) $(DEPS)
	@mkdir -p $(TMPDIR)
	@for f in $(DEPS) $(DUT); do \
		sed 's/import monitor_pkg::\*;//g' $$f > $(TMPDIR)/$$(basename $$f); \
	done
	$(SV2V) $(INC) $(PKGS) \
		$(TMPDIR)/axi_monitor_trans_mgr.sv \
		$(TMPDIR)/axi_monitor_timer.sv \
		$(TMPDIR)/counter_freq_invariant.sv \
		$(TMPDIR)/counter_load_clear.sv \
		$(TMPDIR)/axi_monitor_timeout.sv \
		$(TMPDIR)/axi_monitor_reporter.sv \
		$(TMPDIR)/gaxi_fifo_sync.sv \
		$(TMPDIR)/counter_bin.sv \
		$(TMPDIR)/fifo_control.sv \
		$(TMPDIR)/axi_monitor_base.sv > $@
	@rm -rf $(TMPDIR)

clean:
	rm -rf *_flat.v *_prove *_cover
