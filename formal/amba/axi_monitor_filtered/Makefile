# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi_monitor_filtered
# NOTE: This module wraps axi_monitor_base which is BLOCKED due to the
# multi-driver issue in axi_monitor_trans_mgr. See KNOWN_LIMITATION.md.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        monitor_pkg_stub.sv

DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/counter_load_clear.sv \
        $(REPO_ROOT)/rtl/common/counter_freq_invariant.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/rtl/amba/shared/axi_monitor_timer.sv \
        $(REPO_ROOT)/rtl/amba/shared/axi_monitor_trans_mgr.sv \
        $(REPO_ROOT)/rtl/amba/shared/axi_monitor_timeout.sv \
        $(REPO_ROOT)/rtl/amba/shared/axi_monitor_reporter.sv \
        $(REPO_ROOT)/rtl/amba/shared/axi_monitor_base.sv

DUT := $(REPO_ROOT)/rtl/amba/shared/axi_monitor_filtered.sv

TMPDIR := /tmp/formal_axi_monitor_filtered

.PHONY: prove cover clean

prove: axi_monitor_filtered_flat.v
	sby -f axi_monitor_filtered.sby prove

cover: axi_monitor_filtered_flat.v
	sby -f axi_monitor_filtered.sby cover

# Strip both 'import monitor_pkg::*;' and 'monitor_pkg::' prefix references,
# then run sv2v with the minimal package stub.
axi_monitor_filtered_flat.v: $(DUT) $(PKGS) $(DEPS)
	@mkdir -p $(TMPDIR)
	@for f in $(DEPS) $(DUT); do \
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
		$(TMPDIR)/axi_monitor_filtered.sv > $@
	@rm -rf $(TMPDIR)

clean:
	rm -rf *_flat.v *_prove *_cover
