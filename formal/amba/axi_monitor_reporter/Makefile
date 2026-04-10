# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi_monitor_reporter
# Workflow: sv2v flattens SystemVerilog (packages) -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        monitor_pkg_stub.sv

DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv

DUT := $(REPO_ROOT)/rtl/amba/shared/axi_monitor_reporter.sv

TMPDIR := /tmp/formal_axi_monitor_reporter

.PHONY: prove cover clean

prove: axi_monitor_reporter_flat.v
	sby -f axi_monitor_reporter.sby prove

cover: axi_monitor_reporter_flat.v
	sby -f axi_monitor_reporter.sby cover

axi_monitor_reporter_flat.v: $(DUT) $(PKGS) $(DEPS)
	@mkdir -p $(TMPDIR)
	@for f in $(DEPS) $(DUT); do \
		sed 's/import monitor_pkg::\*;//g' $$f > $(TMPDIR)/$$(basename $$f); \
	done
	$(SV2V) $(INC) $(PKGS) \
		$(TMPDIR)/counter_bin.sv \
		$(TMPDIR)/fifo_control.sv \
		$(TMPDIR)/gaxi_fifo_sync.sv \
		$(TMPDIR)/axi_monitor_reporter.sv > $@
	@rm -rf $(TMPDIR)

clean:
	rm -rf *_flat.v *_prove *_cover
