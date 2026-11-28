# SPDX-License-Identifier: MIT
# memory-controllers MC-028 step A: mc_cmd_arb_bank with the row lane moved into
# mc_row_lane, in lockstep with mc_cmd_arb_bank_pre028 (the core before the move),
# every output every cycle, free inputs. Workflow: sv2v flattens the pair
# (both cores + the generated wrapper) -> sby reads plain Verilog.
REPO_ROOT ?= $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
FLAT            := mc_cmd_arb_bank_pair_flat.v
FLAT_FILELIST   := filelists/pair.f
COMB_STAR := sed -E '/(posedge|negedge)/!s/^([[:space:]]*)always @\(.*\) begin$$/\1always @(*) begin/'
FLAT_POST       := $(COMB_STAR)
include $(REPO_ROOT)/make/formal_flat.mk

TASKS := lane lane_n4 nolane cover
.PHONY: all pair clean $(TASKS)
all: $(TASKS)
# regenerate the wrapper and harness after a port change of the core
pair:
	python3 ../gen_pair.py mc_cmd_arb_bank $(REPO_ROOT)/projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_cmd_arb_bank.sv mc_cmd_arb_bank_pair.sv 
$(TASKS): $(FLAT)
	sby -f mc_cmd_arb_bank_equiv.sby $@
clean:
	rm -rf *_flat.v .flat_build $(addprefix mc_cmd_arb_bank_equiv_,$(TASKS))
