# SPDX-License-Identifier: MIT
# Formal verification Makefile for arbiter_rr_pwm_monbus
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
#
# THIS TASK USED TO PROVE A FORK. The directory held
# arbiter_rr_pwm_monbus_formal.sv -- a hand-copied variant of the RTL, 251
# lines divergent from rtl/amba/monitor/arbiter_rr_pwm_monbus.sv -- plus a
# monitor_pkg_stub.sv, because yosys's own SystemVerilog frontend cannot
# resolve package-typed ports (it DROPS the port and then reports it as
# missing). A proof about a copy proves nothing about the design, and this
# one could not run either way.
#
# sv2v resolves the package types, so the real RTL and the real packages go
# in and the fork is gone.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

INC  := -I$(REPO_ROOT)/rtl/amba/includes

PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_arbiter_pkg.sv

DEPS := $(REPO_ROOT)/rtl/common/arbiter_priority_encoder.sv \
        $(REPO_ROOT)/rtl/common/arbiter_round_robin.sv \
        $(REPO_ROOT)/rtl/common/pwm.sv \
        $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv \
        $(REPO_ROOT)/rtl/amba/monitor/arbiter_monbus_common.sv
DUT  := $(REPO_ROOT)/rtl/amba/monitor/arbiter_rr_pwm_monbus.sv

.PHONY: prove cover all clean

all: prove cover

prove: arbiter_rr_pwm_monbus_flat.v
	sby -f arbiter_rr_pwm_monbus.sby prove

cover: arbiter_rr_pwm_monbus_flat.v
	sby -f arbiter_rr_pwm_monbus.sby cover

# monitor_pkg re-exports sub-package types and trips sv2v "ambiguous
# identifier", so strip the import the way apb4_monitor does.
arbiter_rr_pwm_monbus_flat.v: $(DUT) $(PKGS) $(DEPS)
	@mkdir -p /tmp/formal_arbiter_rr_pwm_monbus
	@for f in $(DEPS) $(DUT); do \
	    sed -e 's/import monitor_pkg::\*;//g' -e 's/monitor_pkg:://g' $$f \
	        > /tmp/formal_arbiter_rr_pwm_monbus/$$(basename $$f); \
	done
	# NO --exclude=Assert here: these modules carry no `ifdef FORMAL
	# properties, only ELABORATION asserts (CLIENTS > 0 and friends), and
	# excluding the conversion leaves `assert (...) else begin ... end`
	# in the output, which yosys cannot parse. Letting sv2v convert them
	# drops exactly the checks that do not belong in a proof anyway.
	$(SV2V) --define=FORMAL $(INC) $(PKGS) \
	    $(addprefix /tmp/formal_arbiter_rr_pwm_monbus/,$(notdir $(DEPS) $(DUT))) > $@
	@rm -rf /tmp/formal_arbiter_rr_pwm_monbus

clean:
	rm -rf arbiter_rr_pwm_monbus_flat.v arbiter_rr_pwm_monbus_prove arbiter_rr_pwm_monbus_cover
