# SPDX-License-Identifier: MIT
# Formal verification Makefile for pumice_rd_cmd_cam
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
PUMICE    := $(REPO_ROOT)/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/pumice-ddr2-lpddr2

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(PUMICE)/rtl/includes
PKGS := $(PUMICE)/rtl/includes/pumice_pkg.sv
# order follows rtl/filelists/fub/pumice_rd_cmd_cam.f, which is the authority
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv
DUT  := $(PUMICE)/rtl/fub/pumice_rd_cmd_cam.sv

.PHONY: prove cover all clean
all: prove cover
prove: cam_flat.v
	sby -f rd_cmd_cam.sby prove
cover: cam_flat.v
	sby -f rd_cmd_cam.sby cover
cam_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@
clean:
	rm -rf *_flat.v cam_flat.v rd_cmd_cam_prove rd_cmd_cam_cover
