# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi_write_engine
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
TMPDIR    := .sv2v_prep

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes \
       -I$(REPO_ROOT)/projects/components/dmas/stream/rtl/includes

# Package files (order matters: dependencies first)
PKGS := $(REPO_ROOT)/rtl/amba/includes/monitor_common_pkg.sv \
        $(REPO_ROOT)/rtl/amba/includes/monitor_arbiter_pkg.sv \
        $(REPO_ROOT)/projects/components/dmas/stream/rtl/includes/stream_pkg.sv

# RTL dependencies (write engine uses gaxi_fifo_sync which needs counter_bin + fifo_control)
DEPS := $(REPO_ROOT)/rtl/common/arbiter_round_robin.sv \
        $(REPO_ROOT)/rtl/common/arbiter_priority_encoder.sv \
        $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/dmas/stream/rtl/fub/axi_write_engine.sv

.PHONY: prove cover clean

prove: axi_write_engine_flat.v
	sby -f axi_write_engine.sby prove

cover: axi_write_engine_flat.v
	sby -f axi_write_engine.sby cover

# sv2v does not honour `// synopsys translate_off` -- it is a comment to sv2v,
# so the hang-diagnostic $display survives into the flat and yosys cannot size
# its $time argument ("Don't know how to detect sign and width for AST_AUTOWIRE").
# Strip those blocks for FORMAL ONLY: simulation reads the original source and
# still gets the prints. The `ifdef ENHANCED_DEBUG` prints need no handling --
# sv2v honours preprocessor directives, so they are already excluded.
DUT_PREP := $(TMPDIR)/axi_write_engine.sv

$(TMPDIR):
	mkdir -p $(TMPDIR)

$(DUT_PREP): $(DUT) | $(TMPDIR)
	sed '/synopsys translate_off/,/synopsys translate_on/d' $< > $@

axi_write_engine_flat.v: $(DUT_PREP) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT_PREP) > $@

clean:
	rm -rf *_flat.v *_prove *_cover $(TMPDIR)
