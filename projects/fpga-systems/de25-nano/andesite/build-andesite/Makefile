#==============================================================================
# de25-nano andesite -- first build, Genesys 2 target
#==============================================================================
# All flow logic is in the global make/fpga_flow.mk; keep this file to
# variables only. `make help` lists targets.
#
#   make lint         verilator --lint-only of the top (Xilinx stubs substituted)
#   make bitstream    Vivado synth/impl/bitgen
#   make program      flash the board (BOARD=genesys2 while the DE25-Nano is en route)
#
# No PHY target exists and none is wanted: the DFI 4.0 pins terminate at an
# observability XOR tree inside the top (see rtl/andesite_char_top.sv), so
# there is nothing to generate before the first `make bitstream`. That is
# deliberate -- the K7 DDR3 PHY cannot serve a DDR4/LPDDR4 controller, and
# the real board's PHY strategy is EMIF-first (Intel), per the ruling
# recorded in the andesite TASK-016 ledger.
#==============================================================================

SELF_DIR  := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT  := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git -C $(SELF_DIR) rev-parse --show-toplevel))
export REPO_ROOT := $(RDS_ROOT)

FLOW      := andesite_ddr4
TOP       := andesite_char_top
FILELIST  := $(SELF_DIR)/rtl/filelists/andesite_char_board.f
BOARD     ?= genesys2

# The controller clock. 100 MHz from the Genesys 2 200 MHz oscillator via
# MMCM (see the top's clock section). Whether andesite_core closes at 100 MHz
# on Kintex-7 IS the experiment -- scoria missed it by 1.26 ns and dropped to
# 80 (scoria BUG-003); this build exists to learn the same number early.
SYS_CLK_HZ ?= 100000000

# Lint uses a DIFFERENT filelist: the top instantiates Xilinx primitives
# (IBUFDS/MMCME2_BASE/BUFG) that Verilator cannot elaborate, so the lint
# list substitutes the shared verilator_xilinx_stubs -- the same split
# build-scoria documents. Neither substitution may reach the synthesis list.
lint flat-filelist lint-decl-order: FILELIST := $(SELF_DIR)/rtl/filelists/andesite_char_board_lint.f

include $(RDS_ROOT)/make/fpga_flow.mk
