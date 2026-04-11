# SPDX-License-Identifier: MIT
# Formal verification Makefile for uart_axil_bridge
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
# Dependencies: uart_rx, uart_tx, axil4_master_rd, axil4_master_wr, gaxi_skid_buffer

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

# Include paths for sv2v preprocessing
INC := -I$(REPO_ROOT)/rtl/amba/includes

# Package files (none needed)
PKGS :=

# RTL dependencies
DEPS := $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv \
        $(REPO_ROOT)/rtl/amba/axil4/axil4_master_rd.sv \
        $(REPO_ROOT)/rtl/amba/axil4/axil4_master_wr.sv \
        $(REPO_ROOT)/projects/components/converters/rtl/uart_to_axil4/uart_rx.sv \
        $(REPO_ROOT)/projects/components/converters/rtl/uart_to_axil4/uart_tx.sv

# Device under test
DUT := $(REPO_ROOT)/projects/components/converters/rtl/uart_to_axil4/uart_axil_bridge.sv

.PHONY: prove cover all clean

all: prove cover

prove: uart_axil_bridge_flat.v
	sby -f uart_axil_bridge.sby prove

cover: uart_axil_bridge_flat.v
	sby -f uart_axil_bridge.sby cover

uart_axil_bridge_flat.v: $(DUT) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
