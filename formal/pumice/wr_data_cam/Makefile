# SPDX-License-Identifier: MIT
# Formal verification Makefile for pumice_wr_data_cam
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SHELL     := /bin/bash
# CI installs the pinned sv2v (v0.0.13) onto PATH (filelist-checks.yml). The
# dev machine keeps the same pinned binary at /mnt/data/tools/sv2v without
# putting it on PATH -- fall back to it so a bare `make formal-pumice` works
# locally. Override with SV2V=<path> if neither applies.
SV2V      ?= $(shell command -v sv2v 2>/dev/null || echo /mnt/data/tools/sv2v)
PUMICE    := $(REPO_ROOT)/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/pumice-ddr2-lpddr2

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(PUMICE)/rtl/includes
PKGS := $(PUMICE)/rtl/includes/pumice_pkg.sv
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv
DUT  := $(PUMICE)/rtl/fub/pumice_wr_data_cam.sv

.PHONY: prove prove_f1 prove_f2 cover all clean
all: prove cover
prove: prove_f1 prove_f2
prove_f1 prove_f2 cover: wr_flat.v
	sby -f wr_data_cam.sby $@
wr_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@
clean:
	rm -rf *_flat.v wr_flat.v wr_data_cam_prove wr_data_cam_cover \
	       wr_data_cam_prove_f1 wr_data_cam_prove_f2
