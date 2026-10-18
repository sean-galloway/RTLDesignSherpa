# SPDX-License-Identifier: MIT
# SPDX-FileCopyrightText: 2026 sean galloway
#
# bridge_wr_rate_buf: write rate-matching buffer on a master's upsized path.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes
PKGS :=
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv
DUT := $(REPO_ROOT)/projects/components/fabric-gen-ip/bridge/rtl/bridge_wr_rate_buf.sv

.PHONY: prove cover all clean

all: prove cover

prove: bridge_wr_rate_buf_flat.v
	sby -f bridge_wr_rate_buf.sby prove

cover: bridge_wr_rate_buf_flat.v
	sby -f bridge_wr_rate_buf.sby cover

bridge_wr_rate_buf_flat.v: $(DUT) $(DEPS)
	$(SV2V) $(INC) $(PKGS) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
