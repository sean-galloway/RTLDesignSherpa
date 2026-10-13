# SPDX-License-Identifier: MIT
# Formal verification Makefile for monbus_arbiter
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
#
# Carries the three properties that used to be runtime assertions inside
# rtl/amba/ocelus/monbus_arbiter.sv (issue #112): grant one-hot, grant[grant_id],
# ready only to the granted client. See formal_monbus_arbiter.sv for the
# configuration choice (input skids off, so A3 is checked on a port).

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v

INC  := -I$(REPO_ROOT)/rtl/amba/includes

PKGS := $(REPO_ROOT)/rtl/amba/includes/ocelus_common_pkg.sv

DEPS := $(REPO_ROOT)/rtl/common/arbiter_priority_encoder.sv \
        $(REPO_ROOT)/rtl/common/arbiter_round_robin.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv
DUT  := $(REPO_ROOT)/rtl/amba/ocelus/monbus_arbiter.sv

.PHONY: prove cover all clean

all: prove cover

prove: monbus_arbiter_flat.v
	sby -f monbus_arbiter.sby prove

cover: monbus_arbiter_flat.v
	sby -f monbus_arbiter.sby cover

monbus_arbiter_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) --define=FORMAL $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf monbus_arbiter_flat.v monbus_arbiter_prove monbus_arbiter_cover

# Regenerate-and-diff self-detection for the committed flat (tooling TASK-026
# house pattern; consumed by bin/formal_status.py --check-flats).
.PHONY: check-flat .check_flat_tmp
check-flat: .check_flat_tmp
	@if [ "$$(tr -s '[:space:]' ' ' < .check_flat_tmp)" = "$$(tr -s '[:space:]' ' ' < monbus_arbiter_flat.v)" ]; then \
		rm -f .check_flat_tmp; \
		echo "flat file is current"; \
	else \
		rm -f .check_flat_tmp; \
		echo "STALE: monbus_arbiter_flat.v does not match the RTL."; \
		echo "Regenerate with: make monbus_arbiter_flat.v"; \
		exit 1; \
	fi

.check_flat_tmp: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) --define=FORMAL $(INC) $(PKGS) $(DEPS) $(DUT) > $@
