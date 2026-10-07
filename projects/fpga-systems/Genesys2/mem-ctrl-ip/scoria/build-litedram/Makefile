#==============================================================================
# Genesys 2 LiteDRAM DDR3 -- the board proof and the A/B yardstick.
# All flow logic is in the global make/fpga_flow.mk; keep this file to
# variables only. `make help` lists targets.
#
#   make regen        regenerate the core (./regen.sh; --bios for the memtest)
#   make lint         verilator --lint-only of the top against the core blackbox
#   make bitstream    Vivado synth/impl/bitgen
#   make program      flash the board
#==============================================================================

SELF_DIR  := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT  := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git -C $(SELF_DIR) rev-parse --show-toplevel))
export REPO_ROOT := $(RDS_ROOT)

FLOW      := litedram_ddr3
TOP       := litedram_ddr3_board_top
FILELIST  := $(SELF_DIR)/rtl/filelists/litedram_ddr3_board.f
BOARD     ?= genesys2
SEQ_DIR   := $(SELF_DIR)/../bin

# Lint uses a DIFFERENT filelist: the generated core is Xilinx-primitive soup
# (OSERDESE2, ODELAYE2, IDELAYCTRL, OBUFDS) that Verilator cannot elaborate, so
# linting the build closure reports 50+ MODMISSING errors saying nothing about
# this design. The lint list substitutes a blackbox stub that regen.sh derives
# FROM the core, so the interface checked is the interface the core has -- and a
# mis-wired port is still caught before Vivado. Target-specific variables reach
# lint's prerequisites (flat-filelist, lint-decl-order) as well.
lint flat-filelist lint-decl-order: FILELIST := $(SELF_DIR)/rtl/filelists/litedram_ddr3_board_lint.f

# Nothing to pre-check: this build has no generated bridge. The core IS
# generated, but by regen.sh on demand -- and regenerating it in a prebuild
# would silently absorb whatever LiteDRAM became that day, which is the trap
# build-perf's REGEN_BRIDGES=0 default exists to avoid. Take a new core
# deliberately: make regen.
PREBUILD :=

include $(RDS_ROOT)/make/fpga_flow.mk

.PHONY: regen
regen:              ## Regenerate the LiteDRAM core + its blackbox (./regen.sh)
	cd $(SELF_DIR) && ./regen.sh $(REGEN_ARGS)
