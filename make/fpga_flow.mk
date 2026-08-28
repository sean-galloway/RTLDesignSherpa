# ==============================================================================
# RDS FPGA flow master Makefile -- the whole flow for one harness build
# ==============================================================================
#
# The ONLY place FPGA build/board/sim logic lives. A build's Makefile sets a few
# variables and includes this file; you should never need to know a tcl script
# name, a Vivado command line, or a pytest path to run the flow.
#
#     FLOW      := ddr2_char                 # names the project + bitstream
#     TOP       := ddr2_char_top             # top module, for lint
#     FILELIST  := $(SELF_DIR)/rtl/filelists/ddr2_char_harness.f
#     SIM_TESTS := $(SELF_DIR)/dv/tests      # pytest target for `make sim`
#     SEQ_DIR   := $(SELF_DIR)/../bin        # sequences, for `make run`
#     RDS_ROOT  := $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))
#     include $(RDS_ROOT)/make/fpga_flow.mk
#
# Everything else is derived and overridable. `make help` lists the real target
# set (generated from the ## comments, so it cannot drift).
#
# Target grammar:
#
#   build     project  synth  bitstream  bitstream-ila  lint
#   board     program  ports  board-info  boards
#   run       sim  run  seq-list
#   inspect   utilization  timing
#   tidy      clean  clean-all
#
# Layout: defaults assume the current layout (fpga/tcl, fpga/bitstream,
# fpga/reports) and fall back to the older flat one (tcl/, bitstream/, reports/)
# so existing flows can adopt this file without moving anything first.
#
# A build that needs a genuinely different recipe overrides the variable, not
# the rule -- e.g. BUILD_TCL := my_build.tcl. If it must replace a rule outright,
# include make/fpga_board.mk instead and keep its own build half.
#
# Handbook: [[fpga/cmn-infra/build-flows]] (the Vivado batch flow),
#           [[fpga/cmn-infra/boards]] (the registry),
#           [[fpga/cmn-infra/sequences]] (what `make run` runs).
# ==============================================================================

SHELL := /bin/bash

ifndef FLOW
$(error FLOW is not set. An FPGA build Makefile must set FLOW before including make/fpga_flow.mk)
endif

SELF_DIR ?= $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
RDS_ROOT ?= $(if $(REPO_ROOT),$(REPO_ROOT),$(shell git rev-parse --show-toplevel))
export REPO_ROOT ?= $(RDS_ROOT)

# ---- Layout ----------------------------------------------------------------
# Prefer the fpga/ subdirectory layout; fall back to flat for older flows.
FPGA_DIR   ?= $(if $(wildcard $(SELF_DIR)/fpga),$(SELF_DIR)/fpga,$(SELF_DIR))
TCL_DIR    ?= $(FPGA_DIR)/tcl
BITSTREAM  ?= $(FPGA_DIR)/bitstream/$(FLOW).bit
ILA_BITSTREAM ?= $(FPGA_DIR)/bitstream/$(FLOW)_ila.bit
REPORTS    ?= $(FPGA_DIR)/reports
# Vivado creates its project under $project_root/build, and project_root is
# FPGA_PROJECT_ROOT below -- so this must track FPGA_DIR or `make clean` would
# miss the very directory the build wrote.
BUILD_DIR  ?= $(FPGA_DIR)/build
PROJECT    ?= $(BUILD_DIR)/vivado_project/$(FLOW).xpr

# ---- Tools -----------------------------------------------------------------
VIVADO       ?= vivado
VIVADO_BATCH ?= $(VIVADO) -mode batch -notrace

# ---- One build per target, enforced -----------------------------------------
# Two Vivado runs on the SAME build directory corrupt each other's project and
# run trees: they share $(SELF_DIR)/fpga/build, both write <proj>.runs/impl_1,
# and neither finishes. It looks like a hung build, not a collision -- the
# processes stay pegged at 100% CPU while the log goes silent for hours.
#
# Observed twice: a build believed dead (pkill reported success, processes
# survived) plus a restart on top of it, ~17 CPU-hours burned across the pair.
#
# The lock is per BUILD DIRECTORY, which is the right granularity: build-mon and
# build-perf own separate fpga/build trees and may run at the same time; two of
# the same target may not. flock releases automatically when the command exits,
# including on kill, so there is no stale lock to clean up by hand -- a PID file
# would need exactly the liveness check that failed us.
BUILD_LOCK      ?= $(SELF_DIR)/.vivado-build.lock
LOCK_EXIT        = 99
VIVADO_LOCKED    = flock -n --conflict-exit-code $(LOCK_EXIT) $(BUILD_LOCK) $(VIVADO_BATCH)

# Turn flock's exit 99 into an explanation rather than a bare failure.
define _lock_hint
	rc=$$?; \
	if [ $$rc -eq $(LOCK_EXIT) ]; then \
	    echo ""; \
	    echo "=====================================================================";\
	    echo " ANOTHER VIVADO BUILD IS ALREADY RUNNING FOR THIS TARGET"; \
	    echo "   build dir : $(SELF_DIR)"; \
	    echo "   lock      : $(BUILD_LOCK)"; \
	    echo ""; \
	    echo " Two builds on one project directory corrupt each other and neither"; \
	    echo " completes. A different target (e.g. the other build-*) is fine --"; \
	    echo " the lock is per build directory."; \
	    echo ""; \
	    echo " In flight:"; \
	    ps -eo pid,etime,time,cmd --no-headers \
	      | grep '[u]nwrapped/lnx64.o/vivado' \
	      | awk '{print "   pid " $$1 "  elapsed " $$2 "  cpu " $$3}' || true; \
	    echo ""; \
	    echo " Wait for it, or stop it and re-check that it is really gone:"; \
	    echo "   pkill -9 -f 'unwrapped/lnx64.o/vivado'"; \
	    echo "   pgrep -cf 'unwrapped/lnx64.o/vivado'   # must print 0 before retrying"; \
	    echo "=====================================================================";\
	fi; \
	exit $$rc
endef
PYTHON       ?= python3
VERILATOR    ?= verilator

# ---- Tcl scripts: DISCOVERED, never enumerated -----------------------------
# Every fpga/tcl/*.tcl becomes a `make tcl-<name>` target the moment it lands --
# same discipline as make/tests.mk globbing test_*.py. There is no list to keep
# in sync, so a new script is runnable without editing any Makefile.
TCL_SCRIPTS := $(sort $(notdir $(wildcard $(TCL_DIR)/*.tcl)))
TCL_NAMES   := $(basename $(TCL_SCRIPTS))
# Helpers included BY other scripts, not run on their own.
TCL_HELPERS ?= filelist_utils
TCL_RUNNABLE := $(filter-out $(TCL_HELPERS),$(TCL_NAMES))

# The four semantic targets map onto conventional script names when present.
# Override the variable if a build names them differently; the rule never
# changes, and a missing script fails with a readable message, not a Vivado one.
PROJECT_TCL ?= $(if $(filter create_project,$(TCL_NAMES)),create_project.tcl,)
SYNTH_TCL   ?= $(if $(filter synth_only,$(TCL_NAMES)),synth_only.tcl,)
BUILD_TCL   ?= $(if $(filter build_all,$(TCL_NAMES)),build_all.tcl,)
ILA_TCL     ?= $(if $(filter build_ila,$(TCL_NAMES)),build_ila.tcl,)

# Vivado reads the layout from the environment rather than guessing it from
# where the script sits, so moving a build does not silently relocate outputs.
#
# Two roots, because a build has two: FPGA_PROJECT_ROOT is where Vivado WRITES
# (build/, reports/, bitstream/) and where its constraints live; FPGA_BUILD_ROOT
# is where the build's SOURCES live (rtl/, rtl-vivado/). They were the same
# directory under the old flat layout, so a tcl could use one for both and be
# right by accident -- and was, until fpga/ split them and every source path
# silently moved. FPGA_FILELIST goes further and hands the tcl the exact
# filelist this Makefile already names, so the compile closure has one authority
# instead of a make variable and a tcl string that must agree.
export FPGA_PROJECT_ROOT := $(FPGA_DIR)
export FPGA_BUILD_ROOT   := $(SELF_DIR)
export FPGA_FILELIST     := $(FILELIST)
# The Makefile is the single authority on the artifact name, so a tcl never
# re-derives it. Recursive '=' on purpose: BITSTREAM is resolved further down,
# and a flow may override it (e.g. encoding a build flavor in the filename).
export FPGA_BITSTREAM     = $(BITSTREAM)

# ---- Host / sim entry points -----------------------------------------------
BAUD      ?= 115200
SEQ_DIR   ?=

# Naming convention, discovered rather than enumerated. Nothing here is a list
# to maintain: drop a file in and its target exists. The prefix declares what a
# file IS, so role is visible in `ls` and discovery is a plain glob.
#
#   SEQ_DIR/run_*.py    -> make run-<name>    a runner (drives a whole plan)
#   SEQ_DIR/seq_*.py    -> make seq-<name>    one sequence, run through a runner
#   HOST_DIR/host_*.py  -> make host-<name>   a standalone host program
#   HOST_DIR/test_*.py  -> pytest, via SIM_TESTS -- never a make target here
#   HOST_DIR/<other>.py -> a library: imported by the above, never run directly
#
# run_*.py in the sequence area: each becomes `make run-<name>`.
RUN_SCRIPTS := $(sort $(wildcard $(SEQ_DIR)/run_*.py))
RUN_NAMES   := $(patsubst run_%,%,$(basename $(notdir $(RUN_SCRIPTS))))
RUN_SCRIPT  ?= $(firstword $(RUN_SCRIPTS))

# seq_*.py are the individual sequences the runner can be asked for by name.
SEQ_SCRIPTS := $(sort $(wildcard $(SEQ_DIR)/seq_*.py))
SEQ_NAMES   := $(patsubst seq_%,%,$(basename $(notdir $(SEQ_SCRIPTS))))

# Host programs: the build's own tools (bring-up, sweeps, captures). The host_
# prefix is what makes a file a program, so a driver or regmap sitting in the
# same directory is excluded by name rather than by inspection -- and a reader
# can tell which is which without opening either.
HOST_DIR ?= $(if $(wildcard $(SELF_DIR)/host),$(SELF_DIR)/host,)
HOST_PROGRAMS := $(sort $(wildcard $(HOST_DIR)/host_*.py))
HOST_NAMES    := $(patsubst host_%,%,$(basename $(notdir $(HOST_PROGRAMS))))

SEQUENCES ?=
SIM_TESTS ?=
SIM_ARGS  ?= -q

# Lint waiver set. These are the harness-integration warnings that are noise on
# a board top (vendor IP, generated cores, wide interconnect); real RTL rules are
# enforced where the RTL lives, not here.
LINT_DEFINES ?= +define+USE_ASYNC_RESET
# PINMISSING: a board top routinely leaves a submodule's OPTIONAL status outputs
# open (monbus group fifo counts/full, compressor tier stats, debug taps). That
# is an integration choice, not a defect, and the module's own tests are where a
# genuinely unconnected port gets caught.
LINT_WAIVERS ?= -Wno-MULTIDRIVEN -Wno-UNUSED -Wno-UNDRIVEN -Wno-WIDTH \
                -Wno-CASEINCOMPLETE -Wno-SELRANGE -Wno-DECLFILENAME \
                -Wno-UNUSEDSIGNAL -Wno-VARHIDDEN -Wno-IMPLICIT \
                -Wno-CASEOVERLAP -Wno-MODDUP -Wno-PINMISSING

include $(RDS_ROOT)/make/fpga_board.mk

.DEFAULT_GOAL := help
.PHONY: help project synth bitstream bitstream-ila lint sim run seq-list \
        utilization timing clean clean-all targets \
        $(addprefix tcl-,$(TCL_RUNNABLE)) $(addprefix run-,$(RUN_NAMES)) \
        $(addprefix seq-,$(SEQ_NAMES)) $(addprefix host-,$(HOST_NAMES))

# Run any discovered tcl by name: `make tcl-capture_ila`.
#
# FPGA_JTAG_SERIAL comes from the board registry so a tcl that touches hardware
# can pin its target instead of taking whatever is first on the chain. Resolved
# per-recipe rather than as a global export: it costs a python call, and only
# the tcl targets need it. An empty result is fine -- the tcl then falls back to
# "any target", which is the right answer for a board with no serial recorded.
define _tcl_rule
tcl-$(1):
	@echo "[tcl] $(1).tcl"
	cd $$(SELF_DIR) && \
	    FPGA_JTAG_SERIAL="$$$$($$(PYTHON) $$(FPGA_BOARD_CLI) --board $$(BOARD) serial)" \
	    $$(VIVADO_BATCH) -source $$(TCL_DIR)/$(1).tcl
endef
$(foreach t,$(TCL_RUNNABLE),$(eval $(call _tcl_rule,$(t))))

# Run any discovered run_*.py by name: `make run-smoke`.
define _run_rule
run-$(1):
	$$(PYTHON) $$(SEQ_DIR)/run_$(1).py --board $$(BOARD) --baud $$(BAUD) \
	    $$(if $$(SEQUENCES),--sequences $$(SEQUENCES),)
endef
$(foreach r,$(RUN_NAMES),$(eval $(call _run_rule,$(r))))

# Run ONE discovered sequence by name: `make seq-memtest`. Goes through the
# runner rather than executing the module, so dependencies (`requires`) are
# still resolved -- running a test sequence without its init would otherwise
# fail somewhere deep instead of being refused up front.
define _seq_rule
seq-$(1):
	@[ -n "$$(RUN_SCRIPT)" ] || \
	    (echo "No run_*.py in SEQ_DIR=$$(SEQ_DIR) to run sequence '$(1)'" && false)
	$$(PYTHON) $$(RUN_SCRIPT) --board $$(BOARD) --baud $$(BAUD) --sequences $(1)
endef
$(foreach s,$(SEQ_NAMES),$(eval $(call _seq_rule,$(s))))

# Run any discovered host program by name: `make host-bringup_joint_probe`.
# ARGS passes through, since these take flow-specific options.
ARGS ?=
define _host_rule
host-$(1):
	$$(PYTHON) $$(HOST_DIR)/host_$(1).py $$(ARGS)
endef
$(foreach h,$(HOST_NAMES),$(eval $(call _host_rule,$(h))))

targets:            ## Show what was DISCOVERED on disk (tcl, runners, sequences, host tools)
	@echo "tcl scripts in $(TCL_DIR):"
	@$(if $(TCL_RUNNABLE),for t in $(TCL_RUNNABLE); do echo "    make tcl-$$t"; done,echo "    (none)")
	@echo "  helpers (sourced, not run): $(if $(TCL_HELPERS),$(TCL_HELPERS),none)"
	@echo "runners in $(SEQ_DIR):"
	@$(if $(RUN_NAMES),for r in $(RUN_NAMES); do echo "    make run-$$r"; done,echo "    (none)")
	@echo "sequences in $(SEQ_DIR):"
	@$(if $(SEQ_NAMES),for s in $(SEQ_NAMES); do echo "    make seq-$$s"; done,echo "    (none)")
	@echo "host programs in $(if $(HOST_DIR),$(HOST_DIR),<no host/ dir>):"
	@$(if $(HOST_NAMES),for h in $(HOST_NAMES); do echo "    make host-$$h"; done,echo "    (none)")
	@echo "semantic targets -> script:"
	@echo "    project       $(if $(PROJECT_TCL),$(PROJECT_TCL),MISSING)"
	@echo "    synth         $(if $(SYNTH_TCL),$(SYNTH_TCL),MISSING)"
	@echo "    bitstream     $(if $(BUILD_TCL),$(BUILD_TCL),MISSING)"
	@echo "    bitstream-ila $(if $(ILA_TCL),$(ILA_TCL),MISSING)"

# A semantic target whose script is absent should say so, not hand Vivado an
# empty -source argument.
_require_tcl = @[ -n "$(1)" ] || (echo "No $(2) script found in $(TCL_DIR) -- \
	set $(3) or add one (make targets shows what was discovered)." && false)

# ---- Help (generated from ## comments, so it cannot go stale) --------------
help:               ## Show this message
	@echo "$(FLOW) -- FPGA flow (BOARD=$(BOARD))"
	@echo ""
	@grep -hE '^[a-zA-Z0-9_-]+:.*?## .*$$' $(MAKEFILE_LIST) \
	    | sort -u \
	    | awk 'BEGIN {FS = ":.*?## "}; {printf "  \033[36m%-16s\033[0m %s\n", $$1, $$2}'
	@echo ""
	@echo "  bitstream -> $(BITSTREAM)"
	@echo "  reports   -> $(REPORTS)"

# ---- Build -----------------------------------------------------------------
# Declaration-order gate. Verilator does NOT catch this class and Vivado only
# WARNS (Synth 8-8895), so it reaches a bitstream:
#
#   an identifier used in a module port map before it is declared becomes an
#   IMPLICIT 1-BIT WIRE.
#
# That silently truncated a 32-bit APB address and data bus to one bit in
# stream_harness -- the observer and slave-monitor register blocks could not be
# configured at all on silicon, while every cosim passed, because Verilator
# resolves the later declaration instead of truncating. Days were spent
# debugging monitors that were fine.
#
# Scope is MODULES: *_pkg.sv is excluded because the checker conflates package
# scopes (struct fields, enum members, function locals) and reports false
# positives there -- and a package has no port map, so the implicit-net class
# cannot occur in one.
DECL_ORDER_CHECK ?= $(RDS_ROOT)/bin/check_sv_decl_order.py
DECL_FILES       ?= $(SELF_DIR)/.decl_order_files.txt

# Lint the configuration this build ACTUALLY SYNTHESIZES, not the RTL defaults.
#
# Vivado applies these as generics from the same env vars (see
# fpga/tcl/create_project.tcl). Verilator was given none of them, so lint ran
# against whatever the top declared -- for stream that is NUM_CHANNELS=4, while
# build-perf synthesizes 8. A gate that checks a different configuration than
# the one being built cannot catch a configuration-specific fault, and this flow
# has already shipped one such fault to silicon (implicit 1-bit APB nets, now
# covered by lint-decl-order). Keep this list in step with create_project.tcl.
LINT_GENERICS = \
    $(if $(STREAM_NUM_CHANNELS),-GNUM_CHANNELS=$(STREAM_NUM_CHANNELS)) \
    $(if $(USE_AXI_MONITORS),-GUSE_AXI_MONITORS=$(USE_AXI_MONITORS)) \
    $(if $(MON_N_PROFILE),-GMON_N_PROFILE=$(MON_N_PROFILE)) \
    $(if $(MON_ERROR_FLAVOR),-GMON_ERROR_FLAVOR=$(MON_ERROR_FLAVOR)) \
    $(if $(STREAM_CLKOUT0_DIVIDE),-GCLKOUT0_DIVIDE=$(STREAM_CLKOUT0_DIVIDE))

lint: lint-decl-order   ## verilator --lint-only of the whole harness (fast, pre-Vivado)
	@[ -n "$(TOP)" ] || (echo "TOP is not set -- cannot lint." && false)
	@[ -f "$(FILELIST)" ] || (echo "FILELIST not found: $(FILELIST)" && false)
	@echo "[lint] $(TOP) $(if $(strip $(LINT_GENERICS)),[$(strip $(LINT_GENERICS))],[RTL defaults])"
	@$(VERILATOR) --lint-only --top-module $(TOP) -f $(FILELIST) \
	    $(LINT_GENERICS) $(LINT_DEFINES) $(LINT_WAIVERS)

lint-decl-order:    ## signals must be declared before use (implicit 1-bit nets)
	@[ -f "$(DECL_ORDER_CHECK)" ] || (echo "missing $(DECL_ORDER_CHECK)" && false)
	@echo "[lint] declaration order ($(TOP))"
	@RDS_ROOT_ENV="$(RDS_ROOT)" FL="$(FILELIST)" $(PYTHON) -c \
	  "import os; from TBClasses.shared.filelist_utils import get_sources_from_filelist as G; \
	   s,_ = G(repo_root=os.environ['RDS_ROOT_ENV'], filelist_path=os.environ['FL']); \
	   print(chr(10).join(f for f in s if f.endswith('.sv') and not f.endswith('_pkg.sv')))" \
	  > $(DECL_FILES) || (echo "could not resolve the filelist closure -- refusing to skip the check" && false)
	@$(PYTHON) $(DECL_ORDER_CHECK) $$(cat $(DECL_FILES)) && rm -f $(DECL_FILES)

# Optional pre-build step. Some flows must regenerate collateral before any
# synthesis -- a generated bridge from its .toml, a register block from its
# .rdl -- or a stale checkout silently produces a stale bitstream. Rather than
# every such flow growing its own recipe (which is how per-flow Makefiles start
# diverging again), a build declares the command and this file wires it in:
#
#     PREBUILD := bash $(FRAMEWORK_ROOT)/bin/regen_bridges.sh my_bridge
#
# Empty by default, so a flow that needs nothing adds nothing.
PREBUILD ?=

.PHONY: prebuild
prebuild:           ## Run the flow's PREBUILD step, if it declared one
ifneq ($(strip $(PREBUILD)),)
	@echo "[prebuild] $(PREBUILD)"
	@$(PREBUILD)
endif

project synth bitstream bitstream-ila: prebuild

project:            ## Create the Vivado project (no build)
	$(call _require_tcl,$(PROJECT_TCL),create_project,PROJECT_TCL)
	@echo "[project] $(FLOW)"
	@cd $(SELF_DIR) && $(VIVADO_LOCKED) -source $(TCL_DIR)/$(PROJECT_TCL) || { \
	    $(_lock_hint); }

synth:              ## Synthesis only + utilization + failing-path reports
	$(call _require_tcl,$(SYNTH_TCL),synth,SYNTH_TCL)
	@echo "[synth] $(FLOW) (skip place/route)"
	@cd $(SELF_DIR) && $(VIVADO_LOCKED) -source $(TCL_DIR)/$(SYNTH_TCL) || { \
	    $(_lock_hint); }
	@$(MAKE) --no-print-directory utilization
	@$(MAKE) --no-print-directory timing

bitstream:          ## Full synth/impl/bitgen + all reports (10-30 min)
	$(call _require_tcl,$(BUILD_TCL),build,BUILD_TCL)
	@echo "[bitstream] $(FLOW) full flow"
	@cd $(SELF_DIR) && $(VIVADO_LOCKED) -source $(TCL_DIR)/$(BUILD_TCL) || { \
	    $(_lock_hint); }
	@echo ""
	@echo "Bitstream: $(BITSTREAM)"
	@echo "Reports:   $(REPORTS)"

bitstream-ila:      ## Same design plus an ILA on the marked debug nets
	$(call _require_tcl,$(ILA_TCL),ILA build,ILA_TCL)
	@echo "[bitstream-ila] $(FLOW)"
	@cd $(SELF_DIR) && $(VIVADO_LOCKED) -source $(TCL_DIR)/$(ILA_TCL) || { \
	    $(_lock_hint); }
	@echo ""
	@echo "ILA bitstream: $(ILA_BITSTREAM) (+ .ltx probes)"

# ---- Sim + sequences -------------------------------------------------------
sim:                ## Run this build's harness sim (cocotb, no board)
	@[ -n "$(SIM_TESTS)" ] || (echo "SIM_TESTS is not set -- nothing to simulate." && false)
	@echo "[sim] $(SIM_TESTS)"
	cd $(REPO_ROOT) && $(PYTHON) -m pytest $(SIM_TESTS) $(SIM_ARGS)

# `run` drives a PROGRAMMED board through the area's sequences. Port discovery
# is the run script's job (board registry + identity probe), so no UART= here.
run:                ## Run sequences on the board (SEQUENCES="init write_read")
	@[ -n "$(RUN_SCRIPT)" ] || \
	    (echo "No run_*.py found in SEQ_DIR=$(SEQ_DIR)" && false)
	$(PYTHON) $(RUN_SCRIPT) --board $(BOARD) --baud $(BAUD) \
	    $(if $(SEQUENCES),--sequences $(SEQUENCES),)

seq-list:           ## List the sequences this area offers
	@[ -n "$(RUN_SCRIPT)" ] || \
	    (echo "No run_*.py found in SEQ_DIR=$(SEQ_DIR)" && false)
	@$(PYTHON) $(RUN_SCRIPT) --list

# ---- Report shortcuts ------------------------------------------------------
utilization:        ## Print the latest utilization report
	@if [ -f $(REPORTS)/utilization_impl.txt ]; then \
	    echo "=== Post-route utilization ==="; \
	    sed -n '/Slice LUTs\|Slice Registers\|Block RAM Tile\|DSPs\|LUT as Logic\|LUT as Memory/,+0p' \
	        $(REPORTS)/utilization_impl.txt | head -60; \
	elif [ -f $(REPORTS)/utilization_synth.txt ]; then \
	    echo "=== Post-synth utilization (impl not yet run) ==="; \
	    sed -n '/Slice LUTs\|Slice Registers\|Block RAM Tile\|DSPs\|LUT as Logic\|LUT as Memory/,+0p' \
	        $(REPORTS)/utilization_synth.txt | head -60; \
	else \
	    echo "No utilization report yet -- run 'make synth' or 'make bitstream'."; \
	fi

# The WNS/WHS table sits ~150 lines into the report, well past the Timer
# Settings preamble -- so `head` showed the settings and never the verdict, which
# is the one thing this target exists to print. Cut to the summary row plus the
# met/not-met line instead.
_timing_verdict = \
	    grep -m1 -A3 'WNS(ns)' $(1) || true; \
	    grep -m1 -E 'All user specified timing constraints are met|Timing constraints are not met' $(1) || true

timing:             ## Print the latest timing summary + failing hotspots
	@if [ -f $(REPORTS)/timing_summary.txt ]; then \
	    echo "=== Post-route timing summary ==="; \
	    $(call _timing_verdict,$(REPORTS)/timing_summary.txt); \
	elif [ -f $(REPORTS)/timing_summary_synth.txt ]; then \
	    echo "=== Post-synth timing summary ==="; \
	    $(call _timing_verdict,$(REPORTS)/timing_summary_synth.txt); \
	else \
	    echo "No timing report yet -- run 'make synth' or 'make bitstream'."; \
	fi
	@if [ -f $(REPORTS)/timing_failing_hotspots.txt ]; then \
	    echo ""; echo "=== Failing-endpoint hotspots ==="; \
	    head -20 $(REPORTS)/timing_failing_hotspots.txt; \
	fi

# ---- Keep --------------------------------------------------------------
# `clean` treats the build dir as disposable, which is correct -- so nothing
# worth keeping may live there. This promotes the current build into the area's
# `stable/` sibling, which no clean target touches and which IS tracked.
# One slot: it overwrites. See <area>/stable/MANIFEST.md.
STABLE_DIR ?= $(SELF_DIR)/../stable

.PHONY: keep
keep:               ## Copy this build's bitstream + reports to ../stable/
	@[ -f "$(BITSTREAM)" ] || \
	    (echo "[keep] no bitstream at $(BITSTREAM) -- build first" && false)
	@echo "[keep] $(FLOW) -> $(STABLE_DIR)"
	@mkdir -p $(STABLE_DIR)/bitstream $(STABLE_DIR)/reports
	@rm -f $(STABLE_DIR)/bitstream/* $(STABLE_DIR)/reports/*
	@cp $(BITSTREAM) $(STABLE_DIR)/bitstream/
	@[ -d "$(REPORTS)" ] && cp -r $(REPORTS)/. $(STABLE_DIR)/reports/ || true
	@echo "[keep] copied. NOW UPDATE $(STABLE_DIR)/MANIFEST.md -- a stable"
	@echo "[keep] artifact with a stale manifest is worse than none: it"
	@echo "[keep] describes a build that is no longer there."

# ---- Clean -----------------------------------------------------------------
# Refuses to delete anything git is tracking. The build dirs are ignored (see
# .gitignore, build-*/fpga/) so this should never trigger -- but it has cost a
# verified bitstream more than once, and a guard that never fires is cheap.
clean:              ## Remove Vivado artifacts, reports and the bitstream
	@echo "[clean] $(FLOW)"
	@tracked=$$(cd $(REPO_ROOT) && git ls-files --error-unmatch \
	    $(BUILD_DIR) $(REPORTS) $(BITSTREAM) $(ILA_BITSTREAM) 2>/dev/null); \
	 if [ -n "$$tracked" ]; then \
	    echo "[clean] REFUSING -- these are tracked in git:"; \
	    echo "$$tracked" | sed 's/^/  /'; \
	    echo "[clean] A build dir must not hold tracked files. Move what is"; \
	    echo "[clean] worth keeping to ../stable (make keep) and untrack these."; \
	    exit 1; \
	 fi
	rm -rf $(BUILD_DIR) $(REPORTS) $(SELF_DIR)/.Xil
	rm -f  $(BITSTREAM) $(ILA_BITSTREAM)
	rm -f  $(SELF_DIR)/vivado.log $(SELF_DIR)/vivado.jou
	rm -f  $(SELF_DIR)/vivado_*.backup.log $(SELF_DIR)/vivado_*.backup.jou
	rm -f  $(SELF_DIR)/vivado_pid*.str $(SELF_DIR)/hs_err_pid*.log

# Verilator build trees for this area's cosims. fpga_flow.mk had NO target for
# these -- `clean` only removes Vivado artifacts -- so anyone wanting a cold
# cosim typed `rm -rf .../local_sim_build` by hand, which is precisely the
# blunt recursive delete that has taken out other sessions' in-flight builds
# (vault/Tasks/amba/open.md). Having the target exist is most of the fix: the
# hand-rolled command was written because there was nothing to call.
.PHONY: clean-build
clean-build:        ## Remove cosim Verilator build trees (skips live runs)
	@$(PYTHON) $(REPO_ROOT)/bin/clean_sim_builds.py $(SELF_DIR)

clean-all: clean clean-build   ## clean + sim builds + logs + Python bytecode
	@echo "[clean-all] $(FLOW)"
	@find $(SELF_DIR) -type d -name __pycache__ -exec rm -rf {} + 2>/dev/null || true
	@find $(SELF_DIR) -type f -name "*.pyc" -delete 2>/dev/null || true
