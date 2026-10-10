# SPDX-License-Identifier: MIT
# Formal verification Makefile for scoria_rd_cmd_cam
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
SCORIA    := $(REPO_ROOT)/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/scoria-ddr3-lpddr3

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(SCORIA)/rtl/includes
PKGS := $(SCORIA)/rtl/includes/scoria_pkg.sv
# order follows rtl/filelists/fub/scoria_rd_cmd_cam.f, which is the authority
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv
DUT  := $(SCORIA)/rtl/fub/scoria_rd_cmd_cam.sv

.PHONY: prove cover all clean
all: prove cover
prove: cam_flat.v
	sby -f scoria_rd_cmd_cam.sby prove
cover: cam_flat.v
	sby -f scoria_rd_cmd_cam.sby cover
cam_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@
clean:
	rm -rf *_flat.v cam_flat.v rd_cmd_cam_prove rd_cmd_cam_cover

# tooling TASK-026: regenerate-and-diff self-detection for the committed flat.
# House pattern from formal/common/counter_freq_invariant; consumed by
# bin/formal_status.py --check-flats (mechanism a) and the pre-commit gate.
# Comparison squeezes whitespace, matching the token normalization the
# checker uses (committed flats may be post-formatter).
.PHONY: check-flat .check_flat_tmp
check-flat: .check_flat_tmp
	@if [ "$$(tr -s '[:space:]' ' ' < .check_flat_tmp)" = "$$(tr -s '[:space:]' ' ' < cam_flat.v)" ]; then \
		rm -f .check_flat_tmp; \
		echo "flat file is current"; \
	else \
		rm -f .check_flat_tmp; \
		echo "STALE: cam_flat.v does not match the RTL."; \
		echo "Regenerate with: make cam_flat.v"; \
		exit 1; \
	fi

.check_flat_tmp: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@