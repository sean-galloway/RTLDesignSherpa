# SPDX-License-Identifier: MIT
# Formal verification Makefile for axi_split_combi
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
SRCS := $(REPO_ROOT)/rtl/amba/shared/axi_split_combi.sv
TMPDIR := /tmp/formal_axi_split_combi

.PHONY: prove cover all clean

all: prove cover

prove: axi_split_combi_flat.v
	sby -f axi_split_combi.sby prove

cover: axi_split_combi_flat.v
	sby -f axi_split_combi.sby cover

axi_split_combi_flat.v: $(PKGS) $(SRCS)
	@mkdir -p $(TMPDIR)
	@for f in $(SRCS); do cp $$f $(TMPDIR)/; done
	$(SV2V) --define=FORMAL $(INC) $(PKGS) $(addprefix $(TMPDIR)/,$(notdir $(SRCS))) > $@
	@rm -rf $(TMPDIR)

clean:
	rm -rf axi_split_combi_prove axi_split_combi_cover
