# SPDX-License-Identifier: MIT
# memory-controllers MC-028 step A: mc_cmd_arb_frfcfs with the row lane moved into
# mc_row_lane, in lockstep with mc_cmd_arb_frfcfs_pre028 (the core before the move),
# every output every cycle, free inputs. Workflow: sv2v flattens the pair
# (both cores + the generated wrapper) -> sby reads plain Verilog.
REPO_ROOT ?= $(shell git rev-parse --show-toplevel)
SV2V      ?= sv2v
FLAT            := mc_cmd_arb_frfcfs_pair_flat.v
FLAT_FILELIST   := filelists/pair.f
COMB_STAR := sed -E '/(posedge|negedge)/!s/^([[:space:]]*)always @\(.*\) begin$$/\1always @(*) begin/'
FLAT_POST       := $(COMB_STAR)
include $(REPO_ROOT)/make/formal_flat.mk

TASKS := lane nolane cover
.PHONY: all pair clean $(TASKS)
all: $(TASKS)
# regenerate the wrapper and harness after a port change of the core. The
# lane's bank / row bus idles at whatever the lane last loaded (it is read
# only with row2_act_o / row2_pre_o), so it compares only while gold fires.
pair:
	python3 ../gen_pair.py mc_cmd_arb_frfcfs $(REPO_ROOT)/projects/components/mem-ctrl-ip/common-ip/rtl/fub/mc_cmd_arb_frfcfs.sv mc_cmd_arb_frfcfs_pair.sv --strobe-gated 'row2_bank_o=g_row2_act_o || g_row2_pre_o' --strobe-gated 'row2_row_o=g_row2_act_o || g_row2_pre_o'
$(TASKS): $(FLAT)
	sby -f mc_cmd_arb_frfcfs_equiv.sby $@
clean:
	rm -rf *_flat.v .flat_build $(addprefix mc_cmd_arb_frfcfs_equiv_,$(TASKS))
