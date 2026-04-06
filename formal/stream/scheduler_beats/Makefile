# SPDX-License-Identifier: MIT
# Formal verification Makefile for scheduler_beats (RAPIDS fub_beats variant)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(REPO_ROOT)/projects/components/rapids/rtl/includes

# Package files (order matters: dependencies first)
# NOTE: monitor_pkg.sv re-exports create_monitor_packet from monitor_common_pkg,
# causing sv2v ambiguity. We use a local empty stub (monitor_pkg_stub.sv) instead,
# which satisfies the import without re-exporting duplicate symbols.
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba4_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_amba5_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_arbiter_pkg.sv \
        $(CURDIR)/monitor_pkg_stub.sv \
        $(REPO_ROOT)/projects/components/rapids/rtl/includes/rapids_pkg.sv

# RTL dependencies (scheduler_beats is pure logic + FSM, no submodule instantiations)
DEPS :=

# Device under test
DUT := $(REPO_ROOT)/projects/components/rapids/rtl/fub_beats/scheduler_beats.sv

.PHONY: prove cover clean

prove: scheduler_beats_flat.v
	sby -f scheduler_beats.sby prove

cover: scheduler_beats_flat.v
	sby -f scheduler_beats.sby cover

scheduler_beats_flat.v: $(DUT) $(PKGS)
	$(SV2V) $(INC) $(PKGS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
