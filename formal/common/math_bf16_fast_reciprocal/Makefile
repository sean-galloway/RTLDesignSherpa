# SPDX-License-Identifier: MIT
# Formal verification Makefile for math_bf16_fast_reciprocal
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
#
# This task used to read the RTL directly. Yosys's own SystemVerilog frontend
# cannot parse the constructs this module uses, so the proof never ran at all;
# sv2v handles them, which is the same route apb4_monitor and the wb4 family
# take. Regenerate the flat file whenever the RTL changes -- a stale flat is a
# proof about code that no longer exists.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

DEPS := 
DUT  := $(REPO_ROOT)/rtl/math/math_bf16_fast_reciprocal.sv

.PHONY: prove cover all clean

all: prove cover

prove: math_bf16_fast_reciprocal_flat.v
	sby -f math_bf16_fast_reciprocal.sby prove

cover: math_bf16_fast_reciprocal_flat.v
	sby -f math_bf16_fast_reciprocal.sby cover

math_bf16_fast_reciprocal_flat.v: $(DUT) $(DEPS)
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(DEPS) $(DUT) > $@

clean:
	rm -rf math_bf16_fast_reciprocal_flat.v math_bf16_fast_reciprocal_prove math_bf16_fast_reciprocal_cover
