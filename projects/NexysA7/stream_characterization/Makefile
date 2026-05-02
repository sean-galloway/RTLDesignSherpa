#==============================================================================
# stream_characterization — top-level orchestration
#==============================================================================
# This is the umbrella Makefile that drives all four DMA × bridge flows.
# Each flow has its own Makefile under flows-*/Makefile and is fully
# self-contained for its own bitstream + sweeps + reports + plots. This
# Makefile lets you build / sweep / publish across the whole 2x2 matrix
# in a single command.
#
# Targets:
#   make help                — this message
#   make project-<flow>      — Vivado project (no build) for one flow
#   make synth-<flow>        — synth-only for one flow
#   make bitstream-<flow>    — full P&R + bitstream for one flow
#   make program-<flow>      — flash one flow's bitstream
#   make sim-<flow>          — cocotb regression for one flow
#   make clean-<flow>        — wipe one flow's build artifacts
#
#   make all-bitstreams      — build every flow's bitstream (sequential)
#   make all-clean           — wipe every flow
#   make docs                — regenerate the comparison report (.docx + .pdf)
#
#   <flow> ∈ {stream-bridge, vivado-mcdma, stream-vivado-bridge,
#             vivado-mcdma-vivado-bridge}
#
# Examples:
#   make bitstream-stream-bridge
#   make program-vivado-mcdma
#   make all-bitstreams
#   make docs
#==============================================================================

# REPO_ROOT must be set in the environment (e.g. by sourcing env_python).
# This Makefile does not compute it from relative paths — by design.
ifndef REPO_ROOT
$(error REPO_ROOT is not set. Source the repo's env file (env_python) or export REPO_ROOT manually before running make.)
endif

SELF_DIR := $(patsubst %/,%,$(dir $(abspath $(lastword $(MAKEFILE_LIST)))))
export REPO_ROOT
export CHAR_ROOT := $(SELF_DIR)

# ---- Flow inventory ------------------------------------------------------
# Add new flow dirs here as they come online. The skeleton + the future
# two combos are listed so `make help` shows the full matrix even though
# only the first two have working Makefiles today.
ALL_FLOWS := stream-bridge vivado-mcdma stream-vivado-bridge vivado-mcdma-vivado-bridge

# Map short name → directory name.
DIR_stream-bridge                  := flows-stream-bridge
DIR_vivado-mcdma                   := flows-vivado-mcdma
DIR_stream-vivado-bridge           := flows-stream-vivado-bridge
DIR_vivado-mcdma-vivado-bridge     := flows-vivado-mcdma-vivado-bridge

# Only flows that actually exist on disk get used as build targets.
EXISTING_FLOWS := $(foreach f,$(ALL_FLOWS),$(if $(wildcard $(SELF_DIR)/$(DIR_$(f))/Makefile),$(f)))

.PHONY: help docs all-bitstreams all-clean

help:
	@echo "stream_characterization — DMA × bridge characterization matrix"
	@echo ""
	@echo "Per-flow targets (replace <flow> with one of: $(ALL_FLOWS))"
	@echo "  make project-<flow>      Vivado project only"
	@echo "  make synth-<flow>        Synth-only check"
	@echo "  make bitstream-<flow>    Full build"
	@echo "  make program-<flow>      JTAG flash"
	@echo "  make sim-<flow>          Cocotb regression"
	@echo "  make clean-<flow>        Wipe build artifacts"
	@echo ""
	@echo "Aggregate targets (run across every existing flow)"
	@echo "  make all-bitstreams      Build every flow's bitstream in series"
	@echo "  make all-clean           Wipe every flow"
	@echo ""
	@echo "Documentation"
	@echo "  make docs                Regenerate the comparison writeup"
	@echo "                           (DOCX + PDF in docs/)"
	@echo ""
	@echo "Flows present on disk:    $(EXISTING_FLOWS)"
	@echo "Flows planned (skeleton):  $(filter-out $(EXISTING_FLOWS),$(ALL_FLOWS))"

# ---- Per-flow target factory ---------------------------------------------
# For every flow + every action, generate a "<action>-<flow>" target that
# delegates to the per-flow Makefile.
#
#   make bitstream-stream-bridge   →   $(MAKE) -C flows-stream-bridge bitstream
#   make program-vivado-mcdma      →   $(MAKE) -C flows-vivado-mcdma  program
#   ...
PER_FLOW_ACTIONS := project synth bitstream program sim clean clean-all utilization timing

define FLOW_RULES
.PHONY: $(foreach a,$(PER_FLOW_ACTIONS),$(a)-$(1))
$(foreach a,$(PER_FLOW_ACTIONS),\
$(eval $(a)-$(1):; @echo ">>> [$(1)] make $(a)"; $$(MAKE) -C $(SELF_DIR)/$(DIR_$(1)) $(a)))
endef
$(foreach f,$(EXISTING_FLOWS),$(eval $(call FLOW_RULES,$(f))))

# ---- Aggregate targets ----------------------------------------------------
# Build every flow's bitstream in sequence. Each flow has its own Vivado
# project under flows-*/build/, so the runs are isolated and parallelisable
# in principle (would need -j with care since Vivado is RAM-hungry).
all-bitstreams: $(foreach f,$(EXISTING_FLOWS),bitstream-$(f))
	@echo ""
	@echo "All bitstreams built:"
	@for f in $(EXISTING_FLOWS); do \
	    echo "  $(SELF_DIR)/$(DIR_$$f)/bitstream/*.bit"; \
	done

all-clean: $(foreach f,$(EXISTING_FLOWS),clean-$(f))
	@echo "All flows cleaned."

# ---- Documentation --------------------------------------------------------
docs:
	@echo ">>> Regenerating comparison writeup (DOCX + PDF)"
	cd $(SELF_DIR)/docs && ./generate_pdf.sh
