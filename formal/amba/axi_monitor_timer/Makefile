# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi_monitor_timer
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
#
# This task used to read the RTL directly. Yosys's own SystemVerilog frontend
# cannot parse the constructs this module uses, so the proof never ran at all;
# sv2v handles them, which is the same route apb4_monitor and the wb4 family
# take. Regenerate the flat file whenever the RTL changes -- a stale flat is a
# proof about code that no longer exists.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

DEPS := $(REPO_ROOT)/rtl/common/counter_load_clear.sv \
        $(REPO_ROOT)/rtl/common/counter_freq_invariant.sv
DUT  := $(REPO_ROOT)/rtl/amba/monitor/axi_monitor_timer.sv

.PHONY: prove cover all clean

all: prove cover

prove: axi_monitor_timer_flat.v
	sby -f axi_monitor_timer.sby prove

cover: axi_monitor_timer_flat.v
	sby -f axi_monitor_timer.sby cover

axi_monitor_timer_flat.v: $(DUT) $(DEPS)
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(DEPS) $(DUT) > $@

clean:
	rm -rf axi_monitor_timer_flat.v axi_monitor_timer_prove axi_monitor_timer_cover
