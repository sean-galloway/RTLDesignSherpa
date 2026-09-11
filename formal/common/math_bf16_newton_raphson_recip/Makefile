# SPDX-License-Identifier: MIT
# Formal verification Makefile for math_bf16_newton_raphson_recip
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

DEPS := $(REPO_ROOT)/rtl/math/math_prefix_cell.sv \
        $(REPO_ROOT)/rtl/math/math_prefix_cell_gray.sv \
        $(REPO_ROOT)/rtl/math/math_adder_full.sv \
        $(REPO_ROOT)/rtl/math/math_adder_han_carlson_016.sv \
        $(REPO_ROOT)/rtl/math/math_compressor_4to2.sv \
        $(REPO_ROOT)/rtl/math/math_multiplier_dadda_4to2_008.sv \
        $(REPO_ROOT)/rtl/math/math_bf16_exponent_adder.sv \
        $(REPO_ROOT)/rtl/math/math_bf16_mantissa_mult.sv \
        $(REPO_ROOT)/rtl/math/math_bf16_multiplier.sv \
        $(REPO_ROOT)/rtl/common/shifter_barrel.sv \
        $(REPO_ROOT)/rtl/common/count_leading_zeros.sv \
        $(REPO_ROOT)/rtl/math/math_bf16_adder.sv \
        $(REPO_ROOT)/rtl/math/math_bf16_fast_reciprocal.sv
DUT  := $(REPO_ROOT)/rtl/math/math_bf16_newton_raphson_recip.sv

.PHONY: prove cover all clean

all: prove cover

prove: math_bf16_newton_raphson_recip_flat.v
	sby -f math_bf16_newton_raphson_recip.sby prove

cover: math_bf16_newton_raphson_recip_flat.v
	sby -f math_bf16_newton_raphson_recip.sby cover

math_bf16_newton_raphson_recip_flat.v: $(DUT) $(DEPS)
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(DEPS) $(DUT) > $@

clean:
	rm -rf math_bf16_newton_raphson_recip_flat.v math_bf16_newton_raphson_recip_prove math_bf16_newton_raphson_recip_cover
