# SPDX-License-Identifier: MIT
# Formal verification Makefile for alloc_ctrl_beats (RAPIDS fub_beats)
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(REPO_ROOT)/projects/components/rapids/rtl/includes

# RTL dependencies
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/rapids/rtl/fub_beats/alloc_ctrl_beats.sv

.PHONY: prove cover clean

prove: alloc_ctrl_beats_flat.v
	sby -f alloc_ctrl_beats.sby prove

cover: alloc_ctrl_beats_flat.v
	sby -f alloc_ctrl_beats.sby cover

alloc_ctrl_beats_flat.v: $(DUT) $(DEPS)
	$(SV2V) $(INC) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
