#==============================================================================
# Genesys 2 scoria DDR3 -- the A-side of the A/B, and the first scoria board.
# All flow logic is in the global make/fpga_flow.mk; keep this file to
# variables only. `make help` lists targets.
#
#   make phy          generate the K7DDRPHY (bin/gen_k7ddrphy.py)
#   make lint         verilator --lint-only of the top against the PHY stub
#   make bitstream    Vivado synth/impl/bitgen
#   make program      flash the board
#
# BUILD ORDER MATTERS ONCE: `make phy` before the first `make bitstream`. The
# PHY is generated, not tracked, and Vivado reports a missing module 90 seconds
# into synthesis rather than at the point the file was needed -- the same trap
# build-litedram's regen.sh records for VexRiscv. `make bitstream` depends on
# the PHY so it will build it for you; the note is for when you wonder why the
# first build took three minutes longer.
#==============================================================================

SELF_DIR  := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT  := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git -C $(SELF_DIR) rev-parse --show-toplevel))
export REPO_ROOT := $(RDS_ROOT)

FLOW      := scoria_ddr3
TOP       := scoria_char_top
FILELIST  := $(SELF_DIR)/rtl/filelists/scoria_char_board.f
BOARD     ?= genesys2
SEQ_DIR   := $(SELF_DIR)/../host

# Lint uses a DIFFERENT filelist. The generated PHY is Xilinx-primitive soup
# (OSERDESE2, ISERDESE2, IDELAYE2, ODELAYE2) that Verilator cannot elaborate,
# so linting the build closure reports MODMISSING and says nothing about this
# design. The lint list substitutes a blackbox stub that gen_core_blackbox.py
# derives FROM the generated PHY -- so the interface checked is the interface
# the PHY has, and a mis-wired port is still caught before Vivado.
# Target-specific variables reach lint's prerequisites too.
lint flat-filelist lint-decl-order: FILELIST := $(SELF_DIR)/rtl/filelists/scoria_char_board_lint.f

# The controller clock. 80 MHz, not 100: scoria_top misses 100 MHz by 1.26 ns
# even at high implementation effort (scoria BUG-003), and 80 keeps DDR3 in
# spec -- 4 phases x 80 = 320 MHz CK, tCK 3.125 ns, inside the tCK(AVG) max of
# 3.3 ns (JESD79-3F). 75 MHz is 3.333 ns and OUT of spec; LiteDRAM will
# generate for it anyway, which is why gen_k7ddrphy.py warns rather than
# trusting the tool to refuse.
SYS_CLK_HZ ?= 80000000

# CHECK the generated config bridge against its .toml before any synthesis,
# and do NOT regenerate. pumice learned this the expensive way: regenerating in
# a prebuild means the board design silently absorbs whatever the generator
# became that day, and between its last 75 MHz close and 2026-09-13 three
# generator changes landed and its config bridge grew ~650 flops with nobody
# asking. A board build has to be reproducible from the tree to be worth
# measuring. Drift fails loudly instead.
#
# Take a new bridge deliberately:  REGEN_BRIDGES=1 make bitstream
REGEN_BRIDGES ?= 0
BRIDGE_REGEN  := bash $(SELF_DIR)/../bin/regen_bridges.sh
PREBUILD      := $(BRIDGE_REGEN) $(if $(filter-out 0,$(REGEN_BRIDGES)),,--check)

include $(RDS_ROOT)/make/fpga_flow.mk

# ---- the generated PHY ------------------------------------------------------
PHY_V := $(SELF_DIR)/rtl/generated/k7ddrphy.v
PHY_BB := $(SELF_DIR)/rtl/generated/k7ddrphy_bb.sv

.PHONY: phy
phy: $(PHY_V)   ## Generate the K7DDRPHY + its Verilator blackbox stub

# Needs the LiteX venv built FROM GIT. LITEX_VENV overrides the location; the
# recipe is in the pumice flow's 2026-09-10_tooling_notes.md and the traps are
# in build-litedram/regen.sh.
LITEX_VENV ?= /tmp/claude-1000/litex-venv

$(PHY_V): $(SELF_DIR)/../bin/gen_k7ddrphy.py
	@test -x "$(LITEX_VENV)/bin/python" || { \
	    echo "no LiteX venv at $(LITEX_VENV) -- set LITEX_VENV"; exit 1; }
	"$(LITEX_VENV)/bin/python" $(SELF_DIR)/../bin/gen_k7ddrphy.py \
	    -o $@ --sys-clk-freq $(SYS_CLK_HZ)
	$(PYTHON) $(SELF_DIR)/../bin/gen_core_blackbox.py $@ \
	    -m k7ddrphy -o $(PHY_BB)

# The bitstream needs the PHY to exist. Stated as a dependency rather than left
# to the operator, because the failure is late and misleading.
bitstream: | $(PHY_V)
