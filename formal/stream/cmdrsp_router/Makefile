# SPDX-License-Identifier: MIT
# Formal verification Makefile for cmdrsp_router
# No packages or includes needed, but uses SystemVerilog always_ff/always_comb
# so sv2v converts to plain Verilog for yosys compatibility.

REPO_ROOT := $(shell git rev-parse --show-toplevel)
SV2V      := sv2v

# No include paths needed (no `include directives)
INC :=

# No packages needed
PKGS :=

# No RTL dependencies (pure logic + registers)
DEPS :=

# Device under test
DUT := $(REPO_ROOT)/projects/components/stream/rtl/top/cmdrsp_router.sv

.PHONY: prove cover clean

prove: cmdrsp_router_flat.v
	sby -f cmdrsp_router.sby prove

cover: cmdrsp_router_flat.v
	sby -f cmdrsp_router.sby cover

cmdrsp_router_flat.v: $(DUT)
	$(SV2V) $(INC) $(DUT) > $@

clean:
	rm -rf *_flat.v *_prove *_cover
