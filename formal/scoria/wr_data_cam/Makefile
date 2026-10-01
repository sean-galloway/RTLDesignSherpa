# SPDX-License-Identifier: MIT
# Formal verification Makefile for scoria_wr_data_cam
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
SCORIA    := $(REPO_ROOT)/projects/components/mem-ctrl-ip/scoria-ddr3-lpddr3

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(SCORIA)/rtl/includes
PKGS := $(SCORIA)/rtl/includes/scoria_pkg.sv
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv
DUT  := $(SCORIA)/rtl/fub/scoria_wr_data_cam.sv

.PHONY: prove cover all clean
all: prove cover
prove: wr_flat.v
	sby -f scoria_wr_data_cam.sby prove
cover: wr_flat.v
	sby -f scoria_wr_data_cam.sby cover
wr_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@
clean:
	rm -rf *_flat.v wr_flat.v wr_data_cam_prove wr_data_cam_cover
