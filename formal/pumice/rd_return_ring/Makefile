# SPDX-License-Identifier: MIT
# Formal verification Makefile for pumice_rd_return_ring
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
PUMICE    := $(REPO_ROOT)/projects/components/mem-ctrl-ip/mem-ctrl-research-ip/pumice-ddr2-lpddr2

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(PUMICE)/rtl/includes

# Dependency order follows rtl/filelists/fub/pumice_rd_return_ring.f, which is
# the authority on what this block needs -- not a hand-kept list here.
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv

DUT  := $(PUMICE)/rtl/fub/pumice_rd_return_ring.sv

.PHONY: prove data cover all clean

all: prove cover

# `prove` runs BOTH safety tasks. The split between them is a SOLVER-COST split,
# not a semantic one -- data integrity is a safety property like the rest -- so
# an area-level `make prove-rd_return_ring` must not silently skip it. `data`
# stays as a separate target for iterating on just that family.
prove: ring_flat.v
	sby -f rd_return_ring.sby prove
	sby -f rd_return_ring.sby data

data: ring_flat.v
	sby -f rd_return_ring.sby data

cover: ring_flat.v
	sby -f rd_return_ring.sby cover

ring_flat.v: $(DUT) $(DEPS)
	$(SV2V) $(INC) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v ring_flat.v rd_return_ring_prove rd_return_ring_data rd_return_ring_cover
