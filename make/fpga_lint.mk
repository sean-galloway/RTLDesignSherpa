# ==============================================================================
# RDS FPGA lint -- the pre-Vivado lint gate for one harness build
# ==============================================================================
#
# Split out of make/fpga_flow.mk (2026-10-19) so a flow that keeps its own build
# half -- one that includes make/fpga_board.mk directly, as fpga_flow.mk's
# header allows -- still gets the SAME lint gate instead of none or a copy.
# fpga_flow.mk includes this file; such a flow includes it itself:
#
#     TOP      := my_top                  # top module to lint
#     FILELIST := $(SELF_DIR)/filelists/my_top.f
#     include $(RDS_ROOT)/make/fpga_lint.mk
#
# Needs SELF_DIR, RDS_ROOT, TOP and FILELIST. Targets: lint, flat-filelist,
# lint-decl-order. Flags and waivers are overridable variables, never rules.
# ==============================================================================

PYTHON    ?= python3
VERILATOR ?= verilator

.PHONY: lint flat-filelist lint-decl-order

# Lint waiver set. These are the harness-integration warnings that are noise on
# a board top (vendor IP, generated cores, wide interconnect); real RTL rules are
# enforced where the RTL lives, not here.
LINT_DEFINES ?= +define+USE_ASYNC_RESET
# PINMISSING: a board top routinely leaves a submodule's OPTIONAL status outputs
# open (monbus group fifo counts/full, compressor tier stats, debug taps). That
# is an integration choice, not a defect, and the module's own tests are where a
# genuinely unconnected port gets caught.
#
# IMPLICIT is deliberately NOT waived: an identifier used before any declaration
# silently becomes a 1-bit implicit wire, and Vivado scopes implicit nets per
# module while Verilator merges same-named ones -- so sim lints clean while
# synthesis ties the channel off. That exact fault shipped to the Genesys 2
# amber pair rig (amber BUG-003, undeclared uart_arvalid/uart_arready) despite
# passing every simulation. Verilator runs without -Wno-fatal here, so an
# IMPLICIT warning is a hard lint failure. check_sv_decl_order.py complements
# this by catching use-before-declaration of signals that ARE declared later.
LINT_WAIVERS ?= -Wno-MULTIDRIVEN -Wno-UNUSED -Wno-UNDRIVEN -Wno-WIDTH \
                -Wno-CASEINCOMPLETE -Wno-SELRANGE -Wno-DECLFILENAME \
                -Wno-UNUSEDSIGNAL -Wno-VARHIDDEN \
                -Wno-CASEOVERLAP -Wno-MODDUP -Wno-PINMISSING

# Verilator's loop-unroll budget, when this build's RTL needs more than the
# default. NOT a waiver: BLKLOOPINIT is Verilator refusing to elaborate a
# delayed array assignment it could not unroll, so the gate does not fail on a
# style rule -- it fails to look at the design at all.
#
# Empty by default: a flow whose deepest loop fits the stock budget must not pay
# for a bigger one. A flow that needs it sets LINT_UNROLL from the SAME source
# its cocotb tests read, so the gate and the simulator elaborate one budget.
# Genesys 2 stream is the worked example (build-mon/Makefile).
#
# The failure this closes: `make lint` on stream build-mon exited 22 errors,
# every one BLKLOOPINIT in the monitor's per-slot loops, while all seven cocotb
# run() calls over the same RTL compiled clean -- they passed the budget and the
# gate did not. A gate that cannot elaborate the design cannot gate it.
LINT_UNROLL ?=

# ------------------------------------------------------------------------------
# Flattened, DEDUPLICATED source list -- what verilator must actually be given.
# ------------------------------------------------------------------------------
# Filelists compose with `-f`, and several of them reach the same sub-filelist
# down more than one path. Handed a raw `-f`, verilator therefore compiles the
# same source twice: 66 filelists in this repo self-duplicate, amba_all.f at 322
# redundant entries out of 700, axi4_intf_master_observer.f at 69 of 119.
#
# That is not cosmetic. Two copies of one package means two distinct C++ types
# for one typedef, and the failure surfaces as `no match for operator=` between
# a struct and itself -- which reads exactly like an RTL type error and is not.
# A whole debugging session was spent on that, on both sides of a two-agent
# handoff, before anyone suspected the invocation instead of the code.
#
# The cocotb path was always immune because it resolves sources through
# TBClasses.shared.filelist_utils.get_sources_from_filelist(), which dedupes.
# `make lint` was the one verilator consumer that did not, so lint and sim were
# compiling different designs.
#
# bin/flatten_filelist.py expands the -f tree and dedupes (keeping first
# occurrence, so compile order is preserved). Verified byte-identical to the
# helper's closure on stream build-mon: 158 sources, 158 unique.
FLATTEN_FILELIST ?= $(RDS_ROOT)/bin/flatten_filelist.py
FLAT_FILELIST    ?= $(SELF_DIR)/.flat_filelist.f

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
    $(if $(OBS_ENABLE_MON_TAPS),-GOBS_ENABLE_MON_TAPS=$(OBS_ENABLE_MON_TAPS)) \
    $(if $(MON_ERROR_FLAVOR),-GMON_ERROR_FLAVOR=$(MON_ERROR_FLAVOR)) \
    $(if $(STREAM_CLKOUT0_DIVIDE),-GCLKOUT0_DIVIDE=$(STREAM_CLKOUT0_DIVIDE)) \
    $(if $(STREAM_VCO_MHZ),-GVCO_MHZ=$(STREAM_VCO_MHZ)) \
    $(if $(OBS_MAX_TRANSACTIONS),-GOBS_MAX_TRANSACTIONS=$(OBS_MAX_TRANSACTIONS)) \
    $(if $(OBS_NUM_BANKS),-GOBS_NUM_BANKS=$(OBS_NUM_BANKS)) \
    $(if $(OBS_USE_WDATA_ORDER_Q),-GOBS_USE_WDATA_ORDER_Q=$(OBS_USE_WDATA_ORDER_Q))

lint: lint-decl-order flat-filelist  ## verilator --lint-only of the whole harness (fast, pre-Vivado)
	@[ -n "$(TOP)" ] || (echo "TOP is not set -- cannot lint." && false)
	@echo "[lint] $(TOP) $(if $(strip $(LINT_GENERICS)),[$(strip $(LINT_GENERICS))],[RTL defaults])"
	@$(VERILATOR) --lint-only --top-module $(TOP) -f $(FLAT_FILELIST) \
	    $(LINT_GENERICS) $(LINT_DEFINES) $(LINT_WAIVERS) $(LINT_UNROLL)

flat-filelist:      ## Expand + dedupe FILELIST into $(FLAT_FILELIST) (see above)
	@[ -f "$(FILELIST)" ] || (echo "FILELIST not found: $(FILELIST)" && false)
	@[ -f "$(FLATTEN_FILELIST)" ] || (echo "missing $(FLATTEN_FILELIST)" && false)
	@$(PYTHON) $(FLATTEN_FILELIST) $(FILELIST) --resolve-env --absolute-paths \
	    -o $(FLAT_FILELIST) >/dev/null \
	  || (echo "could not flatten $(FILELIST) -- refusing to lint a raw -f list" && false)
	@n=$$(grep -cvE '^[[:space:]]*#|^[[:space:]]*$$|^\+incdir|^-I' $(FLAT_FILELIST)); \
	 u=$$(grep -vE '^[[:space:]]*#|^[[:space:]]*$$|^\+incdir|^-I' $(FLAT_FILELIST) | sort -u | wc -l); \
	 [ "$$n" = "$$u" ] || (echo "flattened list still has duplicates ($$n entries, $$u unique)" && false); \
	 echo "[flat] $$n sources, deduplicated -> $(FLAT_FILELIST)"

lint-decl-order:    ## signals must be declared before use (implicit 1-bit nets)
	@[ -f "$(DECL_ORDER_CHECK)" ] || (echo "missing $(DECL_ORDER_CHECK)" && false)
	@echo "[lint] declaration order ($(TOP))"
	@RDS_ROOT_ENV="$(RDS_ROOT)" FL="$(FILELIST)" $(PYTHON) -c \
	  "import os; from TBClasses.shared.filelist_utils import get_sources_from_filelist as G; \
	   s,_ = G(repo_root=os.environ['RDS_ROOT_ENV'], filelist_path=os.environ['FL']); \
	   print(chr(10).join(f for f in s if f.endswith('.sv') and not f.endswith('_pkg.sv')))" \
	  > $(DECL_FILES) || (echo "could not resolve the filelist closure -- refusing to skip the check" && false)
	@$(PYTHON) $(DECL_ORDER_CHECK) $$(cat $(DECL_FILES)) && rm -f $(DECL_FILES)
