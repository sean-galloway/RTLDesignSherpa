# SPDX-License-Identifier: MIT
# Formal verification Makefile for apbtodescr
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(REPO_ROOT)/projects/components/stream/rtl/includes

# Package files (order matters: dependencies first)
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/projects/components/stream/rtl/includes/stream_pkg.sv

# RTL dependencies (none - pure logic + FSM)
DEPS :=

# Device under test
DUT := $(REPO_ROOT)/projects/components/stream/rtl/fub/apbtodescr.sv

.PHONY: prove cover clean

prove: apbtodescr_flat.v
	sby -f apbtodescr.sby prove

cover: apbtodescr_flat.v
	sby -f apbtodescr.sby cover

apbtodescr_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
