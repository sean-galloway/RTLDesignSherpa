# ==============================================================================
# RDS FPGA board targets -- programming and port discovery
# ==============================================================================
#
# The board-facing half of the FPGA make infra. Included automatically by
# make/fpga_flow.mk; include it DIRECTLY only when a flow already owns its build
# recipes and wants nothing but the board targets:
#
#     BITSTREAM := $(SELF_DIR)/bitstream/ddr2_char.bit
#     RDS_ROOT  := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))
#     include $(RDS_ROOT)/make/fpga_board.mk
#
# Provides:  program  ports  board-info  boards
#
# Board facts come from the registry in projects/fpga-systems/bin/boards/, never
# from a per-flow tcl. Seven flows each carried a near-identical program_fpga.tcl
# with a hardcoded JTAG serial and its own env-var name to override it; that is
# what this replaces. Switch board with BOARD=genesys2 (or export FPGA_BOARD).
#
# Handbook: [[fpga/cmn-infra/boards]]
# ==============================================================================

ifndef BITSTREAM
$(error BITSTREAM is not set. Set it before including make/fpga_board.mk)
endif

RDS_ROOT ?= $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))

# The shared FPGA layer. Overridable so a checkout that relocates it does not
# need this file edited; the error below names it when it is not where we look.
FPGA_BIN       ?= $(RDS_ROOT)/projects/fpga-systems/bin
FPGA_BOARD_CLI := $(FPGA_BIN)/fpga_board.py

ifeq ($(wildcard $(FPGA_BOARD_CLI)),)
$(error Shared FPGA layer not found at $(FPGA_BIN) -- set FPGA_BIN or REPO_ROOT)
endif

# Target board. `nexys_a7_100t` is this lab's default; the registry knows the
# rest (make boards). FPGA_BOARD is honoured so a shell-wide export works.
BOARD  ?= $(if $(FPGA_BOARD),$(FPGA_BOARD),nexys_a7_100t)
VIVADO ?= vivado
PYTHON ?= python3

# ---- One user per BOARD, enforced ------------------------------------------
# fpga_flow.mk's build lock is keyed on the BUILD DIRECTORY, which is right for
# what it guards -- build-mon and build-perf own separate Vivado project trees
# and must run concurrently. A physical board is not contended that way: it is
# contended by its JTAG chain and its UART. So two areas take two DIFFERENT
# build locks and both drive one board, and everything in this file had no lock
# at all.
#
# 2026-09-30, five minutes apart: a scoria LiteDRAM board proof held
# /dev/ttyUSB0 until 09:34:51 and a rapids 8-channel byte-perf run started on
# the same Genesys 2 at 09:40:04.
#
# The failure that near miss would have produced is why this exists, and it is
# the same one the comment above `program` already describes for the HOLD
# fallback: a harness records the sha256 of the bitstream IT programmed, not what
# is on the device, so a third party reprogramming mid-run leaves a results file
# with no error, no timeout and no golden mismatch -- measuring someone else's
# design. This lock finishes an argument this file already makes.
#
# A command PREFIX, deliberately the same shape as VIVADO_LOCKED, so it composes
# inside the define/eval rules in fpga_flow.mk without quoting games. Keyed on
# the JTAG serial (two boards can share one chain), falling back to the board
# name. Details and the exec/fd-9 reasoning: board_lock.sh's header.
#
# Tracked as tooling TASK-022.
BOARD_LOCK   ?= $(FPGA_BIN)/board_lock.sh
BOARD_LOCKED  = $(BOARD_LOCK) --board $(BOARD) --

.PHONY: program ports board-info boards

# Bitstreams are never committed; the one or two worth keeping live in the HOLD
# dir outside the repo (see `keep` in fpga_flow.mk). So after a `make clean-all`
# the build-dir bitstream is gone and the HOLD copy is the only one left --
# program falls back to it rather than telling you to spend 40 minutes
# rebuilding something you already kept.
#
# It says WHICH file it is programming, every time. Silently programming a
# different bitstream than the one you just built is a worse failure than
# refusing: it is how a board result gets attributed to the wrong design.
RDS_HOLD_DIR ?= /mnt/data/fpga-hold
_HOLD_BIT     = $(RDS_HOLD_DIR)/$(BOARD)/$(FLOW)/$(notdir $(BITSTREAM))

program:            ## Flash BITSTREAM onto BOARD over JTAG (falls back to HOLD)
	@if [ -f "$(BITSTREAM)" ]; then \
	    echo "[program] using FRESH build: $(BITSTREAM)"; \
	elif [ -f "$(_HOLD_BIT)" ]; then \
	    echo "[program] no build-dir bitstream -- using HOLD: $(_HOLD_BIT)"; \
	    echo "[program] this is the KEPT build, not whatever is in the RTL now."; \
	else \
	    echo "No bitstream at $(BITSTREAM) nor $(_HOLD_BIT) -- run 'make bitstream'."; \
	    exit 1; \
	fi
	@bit=$$([ -f "$(BITSTREAM)" ] && echo "$(BITSTREAM)" || echo "$(_HOLD_BIT)"); \
	 $(BOARD_LOCKED) $(PYTHON) $(FPGA_BOARD_CLI) --board $(BOARD) program \
	    --bitstream "$$bit" --vivado $(VIVADO)

ports:              ## Which ttyUSB is this board on right now?
	@$(PYTHON) $(FPGA_BOARD_CLI) --board $(BOARD) ports

board-info:         ## This board's part, JTAG serial, UART serial, gotchas
	@$(PYTHON) $(FPGA_BOARD_CLI) --board $(BOARD) info

boards:             ## List every board in the registry
	@$(PYTHON) $(FPGA_BOARD_CLI) list
