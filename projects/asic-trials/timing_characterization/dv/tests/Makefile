# ==============================================================================
# Timing Characterization dv/tests Umbrella Makefile
# ==============================================================================
#
# Thin wrapper that delegates to the per-tier subdirectory Makefiles.
# Two tiers today: `fub/` (per-block characterization) and `top/`
# (full-design characterization).
#
# PREREQUISITES:
#   source $REPO_ROOT/env_python
#
# Usage:
#   make help                  Show targets
#   make run-fub               Run all FUB-level characterization
#   make run-top               Run top-level characterization
#   make run-all               Both fub + top, sequential
#   make run-all-waves         Both with WAVES=1
#   make clean-all             Clean every subdir's build artifacts
#
# Wave gating: every `-waves` variant just re-invokes the underlying
# target with WAVES=1 in the environment. Mirrors the convention used
# in val/{common,amba,integ_*} and the other components/dv/tests/Makefiles.
# ==============================================================================

SHELL := /bin/bash

ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

SUBDIRS := fub top

.DEFAULT_GOAL := help

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Timing Characterization dv/tests umbrella"
	@echo "================================================================================"
	@echo "  make run-fub                    Run all FUB characterization tests"
	@echo "  make run-fub-waves              Same with WAVES=1"
	@echo "  make run-fub-parallel           FUB tests in parallel"
	@echo "  make run-fub-parallel-waves     FUB parallel with waves"
	@echo ""
	@echo "  make run-top                    Run top-level characterization"
	@echo "  make run-top-waves              Same with WAVES=1"
	@echo "  make run-top-parallel           Top tests in parallel"
	@echo "  make run-top-parallel-waves     Top parallel with waves"
	@echo ""
	@echo "  make run-all                    Run fub + top sequentially"
	@echo "  make run-all-waves              Same with WAVES=1"
	@echo ""
	@echo "  make clean-all                  Clean every subdir's build artifacts"
	@echo ""
	@echo "  make fub-<target>               Forward <target> to fub/Makefile"
	@echo "  make top-<target>               Forward <target> to top/Makefile"
	@echo "================================================================================"

# Tier shortcuts. The fub/ Makefile uses `run` (not `run-all`) for its
# default suite; top/ uses `run` likewise.
.PHONY: run-fub run-fub-parallel
run-fub:
	@$(MAKE) --no-print-directory -C fub run
run-fub-parallel:
	@$(MAKE) --no-print-directory -C fub run-parallel

.PHONY: run-top run-top-parallel
run-top:
	@$(MAKE) --no-print-directory -C top run
run-top-parallel:
	@$(MAKE) --no-print-directory -C top run-parallel

.PHONY: run-all
run-all: run-fub run-top

# Generic delegation: `make fub-<anything>` runs `<anything>` inside fub/.
# Combined with the `%-waves` pattern below, every subdir target picks up
# its waves variant for free, e.g. `make fub-run-all-gate-waves`.
fub-%:
	@$(MAKE) --no-print-directory -C fub $*

top-%:
	@$(MAKE) --no-print-directory -C top $*

.PHONY: clean-all
clean-all:
	@for d in $(SUBDIRS); do \
	    echo "[clean-all] $$d/"; \
	    $(MAKE) --no-print-directory -C $$d clean-all || true; \
	done

# ==============================================================================
# Pattern-rule fallback for `-waves` variants. Same idiom as
# val/{common,amba,integ_*}: any existing target gains a `-waves` form by
# prepending WAVES=1 in the environment.
# ==============================================================================
%-waves:
	@$(MAKE) --no-print-directory $* WAVES=1
