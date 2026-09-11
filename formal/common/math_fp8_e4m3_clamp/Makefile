# SPDX-License-Identifier: MIT
# Formal verification Makefile for math_fp8_e4m3_clamp
# Workflow: sv2v flattens the REAL RTL -> sby reads plain Verilog (plain prep).
#
# This task used to prove a hand-copied FORK of the RTL (<module>_formal.sv), kept
# because yosys's own SystemVerilog frontend could not read the real module.
# sv2v can, so the fork is gone and the proof is about the shipped design.
# Regenerate the flat file whenever the RTL changes. (2026-09-11)

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v
INC  := -I$(REPO_ROOT)/rtl/amba/includes
PKGS := 
SRCS := $(REPO_ROOT)/rtl/math/math_fp8_e4m3_clamp.sv
TMPDIR := /tmp/formal_math_fp8_e4m3_clamp

.PHONY: prove cover all clean

all: prove cover

prove: math_fp8_e4m3_clamp_flat.v
	sby -f math_fp8_e4m3_clamp.sby prove

cover: math_fp8_e4m3_clamp_flat.v
	sby -f math_fp8_e4m3_clamp.sby cover

math_fp8_e4m3_clamp_flat.v: $(PKGS) $(SRCS)
	@mkdir -p $(TMPDIR)
	@for f in $(SRCS); do cp $$f $(TMPDIR)/; done
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(addprefix $(TMPDIR)/,$(notdir $(SRCS))) > $@
	@rm -rf $(TMPDIR)

clean:
	rm -rf math_fp8_e4m3_clamp_prove math_fp8_e4m3_clamp_cover
