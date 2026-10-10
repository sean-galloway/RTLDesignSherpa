# SPDX-License-Identifier: MIT
# Formal verification Makefile for scoria_rd_return_ring
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
# See ../bank_timer/Makefile for why the flatten is mandatory here.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
SCORIA    := $(REPO_ROOT)/projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3

INC  := -I$(REPO_ROOT)/rtl/amba/includes -I$(SCORIA)/rtl/includes

# Dependency order follows rtl/filelists/fub/scoria_rd_return_ring.f, which is
# the authority on what this block needs -- not a hand-kept list here.
DEPS := $(REPO_ROOT)/rtl/common/counter_bin.sv \
        $(REPO_ROOT)/rtl/common/fifo_control.sv \
        $(REPO_ROOT)/rtl/amba/gaxi/gaxi_fifo_sync.sv

DUT  := $(SCORIA)/rtl/fub/scoria_rd_return_ring.sv

.PHONY: prove data cover all clean

all: prove cover

# `prove` runs BOTH safety tasks. The split between them is a SOLVER-COST split,
# not a semantic one -- data integrity is a safety property like the rest -- so
# an area-level `make prove-rd_return_ring` must not silently skip it. `data`
# stays as a separate target for iterating on just that family.
prove: ring_flat.v
	sby -f scoria_rd_return_ring.sby prove
	sby -f scoria_rd_return_ring.sby data

data: ring_flat.v
	sby -f scoria_rd_return_ring.sby data

cover: ring_flat.v
	sby -f scoria_rd_return_ring.sby cover

ring_flat.v: $(DUT) $(DEPS)
	$(SV2V) $(INC) $(DEPS) $(DUT) > $@

clean:
	rm -rf *_flat.v ring_flat.v rd_return_ring_prove rd_return_ring_data rd_return_ring_cover

# tooling TASK-026: regenerate-and-diff self-detection for the committed flat.
# House pattern from formal/common/counter_freq_invariant; consumed by
# bin/formal_status.py --check-flats (mechanism a) and the pre-commit gate.
# Comparison squeezes whitespace, matching the token normalization the
# checker uses (committed flats may be post-formatter).
.PHONY: check-flat .check_flat_tmp
check-flat: .check_flat_tmp
	@if [ "$$(tr -s '[:space:]' ' ' < .check_flat_tmp)" = "$$(tr -s '[:space:]' ' ' < ring_flat.v)" ]; then \
		rm -f .check_flat_tmp; \
		echo "flat file is current"; \
	else \
		rm -f .check_flat_tmp; \
		echo "STALE: ring_flat.v does not match the RTL."; \
		echo "Regenerate with: make ring_flat.v"; \
		exit 1; \
	fi

.check_flat_tmp: $(DUT) $(DEPS)
	$(SV2V) $(INC) $(DEPS) $(DUT) > $@