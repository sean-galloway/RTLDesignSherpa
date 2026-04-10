# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi4_master_wr_mon
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        monitor_pkg_stub.sv

# Monitor infrastructure (same as axi_monitor_filtered)
MON_DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
            $(REPO_ROOT)/rtl/common/counter_load_clear.sv \
            $(REPO_ROOT)/rtl/common/counter_freq_invariant.sv \
            $(REPO_ROOT)/rtl/common/fifo_control.sv \
            $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
            $(REPO_ROOT)/rtl/amba/shared/axi_monitor_timer.sv \
            $(REPO_ROOT)/rtl/amba/shared/axi_monitor_trans_mgr.sv \
            $(REPO_ROOT)/rtl/amba/shared/axi_monitor_timeout.sv \
            $(REPO_ROOT)/rtl/amba/shared/axi_monitor_reporter.sv \
            $(REPO_ROOT)/rtl/amba/shared/axi_monitor_base.sv \
            $(REPO_ROOT)/rtl/amba/shared/axi_monitor_filtered.sv

# AXI master write wrapper (skid buffers)
AXI_DEPS := $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv \
            $(REPO_ROOT)/rtl/amba/axi4/axi4_master_wr.sv

DUT := $(REPO_ROOT)/rtl/amba/axi4/axi4_master_wr_mon.sv

ALL_DEPS := $(MON_DEPS) $(AXI_DEPS)

TMPDIR := /tmp/formal_axi4_master_wr_mon

.PHONY: prove cover clean

prove: axi4_master_wr_mon_flat.v
	sby -f axi4_master_wr_mon.sby prove

cover: axi4_master_wr_mon_flat.v
	sby -f axi4_master_wr_mon.sby cover

axi4_master_wr_mon_flat.v: $(DUT) $(PKGS) $(ALL_DEPS)
	@mkdir -p $(TMPDIR)
	@for f in $(ALL_DEPS) $(DUT); do \
		sed -e 's/import monitor_pkg::\*;//g' \
		    -e 's/monitor_pkg:://g' $$f > $(TMPDIR)/$$(basename $$f); \
	done
	$(SV2V) $(INC) $(PKGS) \
		$(TMPDIR)/counter_bin.sv \
		$(TMPDIR)/counter_load_clear.sv \
		$(TMPDIR)/counter_freq_invariant.sv \
		$(TMPDIR)/fifo_control.sv \
		$(TMPDIR)/gaxi_fifo_sync.sv \
		$(TMPDIR)/axi_monitor_timer.sv \
		$(TMPDIR)/axi_monitor_trans_mgr.sv \
		$(TMPDIR)/axi_monitor_timeout.sv \
		$(TMPDIR)/axi_monitor_reporter.sv \
		$(TMPDIR)/axi_monitor_base.sv \
		$(TMPDIR)/axi_monitor_filtered.sv \
		$(TMPDIR)/gaxi_skid_buffer.sv \
		$(TMPDIR)/axi4_master_wr.sv \
		$(TMPDIR)/axi4_master_wr_mon.sv > $@
	@rm -rf $(TMPDIR)

clean:
	rm -rf *_flat.v *_prove *_cover
