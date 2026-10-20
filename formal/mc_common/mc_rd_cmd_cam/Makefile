# SPDX-License-Identifier: MIT
# Formal verification Makefile for pumice_rd_cmd_cam
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
MC        := $(REPO_ROOT)/projects/components/mem-ctrl-ip/common-ip

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(MC)/rtl/includes
PKGS := $(MC)/rtl/includes/mc_common_pkg.sv
# order follows rtl/filelists/fub/pumice_rd_cmd_cam.f, which is the authority
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv
DUT  := $(MC)/rtl/fub/mc_rd_cmd_cam.sv

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
