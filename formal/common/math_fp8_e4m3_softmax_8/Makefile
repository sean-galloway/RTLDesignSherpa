# SPDX-License-Identifier: MIT
# Formal verification Makefile for math_fp8_e4m3_softmax_8
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog.
#
# This task was DEFERRED with the note "Yosys does not support unpacked array
# ports". That is still true of yosys's own frontend (verified 2026-09-11),
# but option 2 of that note -- flatten the array ports into packed vectors --
# is exactly what sv2v does, and sv2v is already the repo's formal front end.
# The harness reads the packed form: lane i is bits [W*i +: W].

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

DUT  := $(REPO_ROOT)/rtl/math/math_fp8_e4m3_softmax_8.sv

.PHONY: prove cover all clean

all: prove cover

prove: math_fp8_e4m3_softmax_8_flat.v
	sby -f math_fp8_e4m3_softmax_8.sby prove

cover: math_fp8_e4m3_softmax_8_flat.v
	sby -f math_fp8_e4m3_softmax_8.sby cover

math_fp8_e4m3_softmax_8_flat.v: $(DUT)
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(DUT) > $@

clean:
	rm -rf math_fp8_e4m3_softmax_8_flat.v math_fp8_e4m3_softmax_8_prove math_fp8_e4m3_softmax_8_cover
