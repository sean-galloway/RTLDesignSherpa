# ==============================================================================
# Open-source ASIC synthesis flow for char_top (Yosys + OpenSTA).
# ==============================================================================
#
# The flow has three stages:
#
#   1. yosys  -- read SV, generic-synthesize, technology-map with ABC against
#                a Liberty file the caller provides via LIB_PATH
#   2. sta    -- OpenSTA loads the post-synth netlist + the same Liberty file
#                and emits a per-path-group timing report driven by char_top.sdc
#   3. report -- collect synthesis logs into build/ for diffing across runs
#
# Required environment / make variables:
#
#   LIB_PATH         path to a Liberty (.lib) standard-cell file
#                    (e.g. sky130_fd_sc_hd__tt_025C_1v80.lib)
#   TARGET_FREQ_MHZ  override the SDC default (500)
#
# Optional:
#
#   EN_*             override the EN_* parameters baked into char_top to
#                    isolate a single FUB.  Defaults: all FUBs enabled.
#   TOP              top-level module name (default: char_top)
#
# Typical invocations:
#
#   make synth                                # default 500 MHz, all FUBs
#   make TARGET_FREQ_MHZ=800 EN_MULTIPLIER=0  # 800 MHz, drop multiplier
#   make sta                                  # rerun STA only
#   make clean                                # nuke build/
# ==============================================================================

# ---- Configuration -----------------------------------------------------------
TOP             ?= char_top
RTL_ROOT        := $(realpath ..)
SYN_ROOT        := $(realpath .)
BUILD_DIR       := $(SYN_ROOT)/build

LIB_PATH        ?=
TARGET_FREQ_MHZ ?= 500

# Per-FUB enables (default to 1 = include).  Pass -DEN_*=0 to drop one.
EN_NAND_TREE       ?= 1
EN_INVERTER_CHAIN  ?= 1
EN_XOR_TREE        ?= 1
EN_CARRY_CHAIN     ?= 1
EN_MULTIPLIER      ?= 1
EN_MUX_TREE        ?= 1
EN_QUEUE_DEPTH     ?= 1
EN_CLK_DIVIDER     ?= 1
EN_GRAY_COUNTER    ?= 1

YOSYS_GENERIC_DEFINES := \
    -DEN_NAND_TREE=$(EN_NAND_TREE) \
    -DEN_INVERTER_CHAIN=$(EN_INVERTER_CHAIN) \
    -DEN_XOR_TREE=$(EN_XOR_TREE) \
    -DEN_CARRY_CHAIN=$(EN_CARRY_CHAIN) \
    -DEN_MULTIPLIER=$(EN_MULTIPLIER) \
    -DEN_MUX_TREE=$(EN_MUX_TREE) \
    -DEN_QUEUE_DEPTH=$(EN_QUEUE_DEPTH) \
    -DEN_CLK_DIVIDER=$(EN_CLK_DIVIDER) \
    -DEN_GRAY_COUNTER=$(EN_GRAY_COUNTER)

# Sources: every .sv listed in ../filelists/char_top.f.  The grep filters
# blank lines and comments; the substitution makes paths absolute.
FILELIST := $(RTL_ROOT)/filelists/char_top.f
SOURCES  := $(shell grep -v '^//' $(FILELIST) | grep -v '^\s*$$' | grep -v '^+incdir' \
                                | sed 's|^|$(RTL_ROOT)/|')
INCDIR   := $(RTL_ROOT)/common

# ---- Targets -----------------------------------------------------------------
.PHONY: all synth sta report clean help check-lib

all: report

help:
	@echo "Targets: synth | sta | report | clean | help"
	@echo "Required: LIB_PATH=/path/to/stdcell.lib"
	@echo "Optional: TARGET_FREQ_MHZ=<MHz> EN_<FUB>=<0|1>"

check-lib:
	@if [ -z "$(LIB_PATH)" ]; then \
		echo "ERROR: LIB_PATH not set.  Pass LIB_PATH=/path/to/stdcell.lib"; \
		exit 1; \
	fi
	@if [ ! -f "$(LIB_PATH)" ]; then \
		echo "ERROR: Liberty file not found: $(LIB_PATH)"; \
		exit 1; \
	fi

$(BUILD_DIR):
	mkdir -p $(BUILD_DIR)

# Stage 1: Yosys -- SV read, generic synth, ABC tech-map against LIB_PATH.
synth: check-lib | $(BUILD_DIR)
	@echo "==> Yosys synth (TOP=$(TOP) TARGET=$(TARGET_FREQ_MHZ) MHz)"
	yosys -q \
	    -E $(BUILD_DIR)/yosys.deps \
	    -l $(BUILD_DIR)/yosys.log \
	    -p "tcl yosys_synth.ys $(TOP) $(LIB_PATH) $(BUILD_DIR) $(INCDIR) $(YOSYS_GENERIC_DEFINES) $(SOURCES)"
	@echo "==> Netlist: $(BUILD_DIR)/$(TOP).netlist.v"

# Stage 2: OpenSTA -- load the post-synth netlist + SDC, emit timing reports.
sta: check-lib
	@if [ ! -f "$(BUILD_DIR)/$(TOP).netlist.v" ]; then \
		echo "ERROR: run 'make synth' first"; exit 1; \
	fi
	@echo "==> OpenSTA report"
	sta -no_init -no_splash -exit \
	    -threads max \
	    -i $(SYN_ROOT)/sta_run.tcl \
	    | tee $(BUILD_DIR)/sta.log
	@echo "==> Per-FUB reports in $(BUILD_DIR)/timing/"

report: synth sta
	@echo "==> Synthesis + STA complete.  Summary:"
	@grep -E "^Chip area|^Path Group:|slack|WORST" $(BUILD_DIR)/sta.log || true

clean:
	rm -rf $(BUILD_DIR)

# Pass LIB_PATH and TARGET_FREQ_MHZ through to sub-tcl files.
export LIB_PATH
export TARGET_FREQ_MHZ
export TOP
export BUILD_DIR
export SYN_ROOT
