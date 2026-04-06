# SPDX-License-Identifier: MIT
# Formal verification Makefile for scheduler
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(REPO_ROOT)/projects/components/stream/rtl/includes

# Package files (order matters: dependencies first)
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_arbiter_pkg.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/includes/stream_pkg.sv

# RTL dependencies (scheduler is pure logic + FSM, no submodule instantiations)
DEPS :=

# Device under test
DUT := $(REPO_ROOT)/projects/components/stream/rtl/fub/scheduler.sv

.PHONY: prove cover clean

prove: scheduler_flat.v
	sby -f scheduler.sby prove

cover: scheduler_flat.v
	sby -f scheduler.sby cover

scheduler_flat.v: $(DUT) $(PKGS)
	$(SV2V) $(INC) $(PKGS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
