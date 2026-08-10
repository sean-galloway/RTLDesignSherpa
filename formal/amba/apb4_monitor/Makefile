# SPDX-License-Identifier: MIT
# Formal verification Makefile for apb4_monitor
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
#
# DEPS is the transitive module closure of apb4_monitor (leaves first), regenerated
# by tools/gen_formal_deps.py after the rtl/amba/monitor/ move, the reporter
# split (axi_monitor_reporter_*), and the monitor_trans_cam extraction.  The
# sv2v file list is derived from $(DEPS) so the two cannot drift.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba5_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_arbiter_pkg.sv \
        monitor_pkg_stub.sv

# RTL dependencies (transitive closure of apb4_monitor, leaves first)
DEPS := $(REPO_ROOT)/rtl/amba/monitor/apb_monitor_addr_check.sv \
        $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv

DUT := $(REPO_ROOT)/rtl/amba/apb4/apb4_monitor.sv

TMPDIR := /tmp/formal_apb4_monitor

.PHONY: prove cover clean

prove: apb4_monitor_flat.v
	sby -f apb4_monitor.sby prove

cover: apb4_monitor_flat.v
	sby -f apb4_monitor.sby cover

# Strip `import monitor_pkg::*;` and `monitor_pkg::` scope prefixes (monitor_pkg
# re-exports sub-package types and trips sv2v "ambiguous identifier"), then
# flatten DUT + closure into a single Verilog file.
apb4_monitor_flat.v: $(DUT) $(PKGS) $(DEPS)
	@mkdir -p $(TMPDIR)
	@for f in $(DEPS) $(DUT); do \
		sed -e 's/import monitor_pkg::\*;//g' \
		    -e 's/monitor_pkg:://g' $$f > $(TMPDIR)/$$(basename $$f); \
	done
	$(SV2V) $(INC) $(PKGS) \
		$(addprefix $(TMPDIR)/,$(notdir $(DEPS) $(DUT))) > $@
	@rm -rf $(TMPDIR)

clean:
	rm -rf *_flat.v *_prove *_cover
