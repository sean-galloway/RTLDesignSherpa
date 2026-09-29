# SPDX-License-Identifier: MIT
# Formal verification Makefile for pumice_wr_data_cam
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
PUMICE    := $(REPO_ROOT)/projects/components/mem-ctrl-ip/pumice-ddr2-lpddr2

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(PUMICE)/rtl/includes
PKGS := $(PUMICE)/rtl/includes/pumice_pkg.sv
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv
DUT  := $(PUMICE)/rtl/fub/pumice_wr_data_cam.sv

.PHONY: prove cover all clean
all: prove cover
prove: wr_flat.v
	sby -f wr_data_cam.sby prove
cover: wr_flat.v
	sby -f wr_data_cam.sby cover
wr_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@
clean:
	rm -rf *_flat.v wr_flat.v wr_data_cam_prove wr_data_cam_cover
