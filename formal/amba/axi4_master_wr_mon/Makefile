# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi4_master_wr_mon
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
#
# DEPS is the transitive module closure of axi4_master_wr_mon (leaves first), regenerated
# by tools/gen_formal_deps.py after the rtl/amba/monitor/ move, the reporter
# split (axi_monitor_reporter_*), and the monitor_trans_cam extraction.  The
# sv2v file list is derived from $(DEPS) so the two cannot drift.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        monitor_pkg_stub.sv

# RTL dependencies (transitive closure of axi4_master_wr_mon, leaves first)
DEPS := $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv \
        $(REPO_ROOT)/rtl/amba/axi4/axi4_master_wr.sv \
        $(REPO_ROOT)/rtl/amba/monitor/axi_monitor_addr_check.sv \
        $(REPO_ROOT)/rtl/amba/monitor/axi_monitor_reporter_compl.sv \
        $(REPO_ROOT)/rtl/amba/monitor/axi_monitor_reporter_debug.sv \
        $(REPO_ROOT)/rtl/amba/monitor/axi_monitor_reporter_error.sv \
        $(REPO_ROOT)/rtl/amba/monitor/axi_monitor_reporter_perf.sv \
        $(REPO_ROOT)/rtl/amba/monitor/axi_monitor_reporter_threshold.sv \
        $(REPO_ROOT)/rtl/amba/monitor/axi_monitor_reporter_timeout.sv \
        $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/rtl/amba/monitor/axi_monitor_reporter.sv \
        $(REPO_ROOT)/rtl/amba/monitor/axi_monitor_timeout.sv \
        $(REPO_ROOT)/rtl/common/counter_load_clear.sv \
        $(REPO_ROOT)/rtl/common/counter_freq_invariant.sv \
        $(REPO_ROOT)/rtl/amba/monitor/axi_monitor_timer.sv \
        $(REPO_ROOT)/rtl/amba/monitor/monitor_trans_cam.sv \
        $(REPO_ROOT)/rtl/amba/monitor/axi_monitor_trans_mgr.sv \
        $(REPO_ROOT)/rtl/amba/monitor/axi_monitor_base.sv \
        $(REPO_ROOT)/rtl/amba/monitor/axi_monitor_filtered.sv

DUT := $(REPO_ROOT)/rtl/amba/axi4/axi4_master_wr_mon.sv

TMPDIR := /tmp/formal_axi4_master_wr_mon

.PHONY: prove cover clean

prove: axi4_master_wr_mon_flat.v
	sby -f axi4_master_wr_mon.sby prove

cover: axi4_master_wr_mon_flat.v
	sby -f axi4_master_wr_mon.sby cover

# Strip `import monitor_pkg::*;` and `monitor_pkg::` scope prefixes (monitor_pkg
# re-exports sub-package types and trips sv2v "ambiguous identifier"), then
# flatten DUT + closure into a single Verilog file.
axi4_master_wr_mon_flat.v: $(DUT) $(PKGS) $(DEPS)
	@mkdir -p $(TMPDIR)
	@for f in $(DEPS) $(DUT); do \
		sed -e 's/import monitor_pkg::\*;//g' \
		    -e 's/monitor_pkg:://g' $$f > $(TMPDIR)/$$(basename $$f); \
	done
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) \
		$(addprefix $(TMPDIR)/,$(notdir $(DEPS) $(DUT))) > $@
	@rm -rf $(TMPDIR)

clean:
	rm -rf *_flat.v *_prove *_cover
