# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi_monitor_addr_check
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        monitor_pkg_stub.sv

DUT  := $(REPO_ROOT)/rtl/amba/shared/axi_monitor_addr_check.sv

ALL_DEPS := $(PKGS) $(DUT)

TMPDIR := /tmp/formal_axi_monitor_addr_check

.PHONY: prove cover clean

prove: axi_monitor_addr_check_flat.v
	sby -f axi_monitor_addr_check.sby prove

cover: axi_monitor_addr_check_flat.v
	sby -f axi_monitor_addr_check.sby cover

axi_monitor_addr_check_flat.v: $(DUT) $(PKGS)
	@mkdir -p $(TMPDIR)
	@for f in $(ALL_DEPS); do \
		sed -e 's/import monitor_pkg::\*;//g' \
		    -e 's/monitor_pkg:://g' $$f > $(TMPDIR)/$$(basename $$f); \
	done
	$(SV2V) $(INC) -DSIMULATION \
		$(TMPDIR)/monitor_common_pkg.sv \
		$(TMPDIR)/monitor_amba4_pkg.sv \
		$(TMPDIR)/monitor_pkg_stub.sv \
		$(TMPDIR)/axi_monitor_addr_check.sv > $@.tmp
	mv $@.tmp $@

clean:
	rm -rf *_flat.v *_prove *_cover
