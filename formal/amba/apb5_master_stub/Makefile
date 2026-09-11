# SPDX-License-Identifier: MIT
# Formal verification Makefile for apb5_master_stub
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

DEPS := $(REPO_ROOT)/rtl/amba/gaxi/gaxi_skid_buffer.sv \
        $(REPO_ROOT)/rtl/amba/apb5/apb5_master.sv
DUT  := $(REPO_ROOT)/rtl/amba/apb5/apb5_master_stub.sv

.PHONY: prove cover all clean

all: prove cover

prove: apb5_master_stub_flat.v
	sby -f apb5_master_stub.sby prove

cover: apb5_master_stub_flat.v
	sby -f apb5_master_stub.sby cover

apb5_master_stub_flat.v: $(DUT) $(DEPS)
	$(SV2V) --define=FORMAL --exclude=Assert $(INC) $(DEPS) $(DUT) > $@

clean:
	rm -rf apb5_master_stub_flat.v apb5_master_stub_prove apb5_master_stub_cover
