# SPDX-License-Identifier: MIT
# Formal verification Makefile for wb4_retry
# Workflow: sv2v flattens SystemVerilog -> sby reads plain Verilog
# (same shape as formal/amba/wb4_master/Makefile).

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := /mnt/data/tools/sv2v

INC := -I$(REPO_ROOT)/rtl/amba/includes

PKGS := $(REPO_ROOT)/rtl/amba/wb4/wb4_pkg.sv
DEPS :=
DUT  := $(REPO_ROOT)/rtl/amba/wb4/wb4_retry.sv

.PHONY: prove cover prove_deep cover_deep all clean

all: prove cover prove_deep cover_deep

prove: wb4_retry_flat.v
	sby -f wb4_retry.sby prove

cover: wb4_retry_flat.v
	sby -f wb4_retry.sby cover

# INFLIGHT=2 via chparam on the harness top: the count bounds and the
# in-order hand-back with two entries open.
prove_deep: wb4_retry_flat.v
	sby -f wb4_retry.sby prove_deep

cover_deep: wb4_retry_flat.v
	sby -f wb4_retry.sby cover_deep

wb4_retry_flat.v: $(DUT) $(PKGS) $(DEPS)
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(PKGS) $(DEPS) $(DUT) > $@
	@echo "asserts in flat: $$(grep -c 'assert' $@)"

clean:
	rm -rf *_flat.v *_prove *_cover *_prove_deep *_cover_deep
