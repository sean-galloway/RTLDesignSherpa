# ==============================================================================
# Misc Components dv/tests Umbrella Makefile
# ==============================================================================
#
# Thin wrapper that delegates to the per-tier subdirectory Makefiles.
# Today there's only `fub/`; add a sibling block (and another SUBDIR) when
# `integration/` or `top/` lands.
#
# PREREQUISITES:
#   source $REPO_ROOT/env_python
#
# Usage:
#   make help               Show targets
#   make run-fub            Run all FUB tests
#   make run-fub-waves      Same with WAVES=1
#   make clean-all          Clean every subdir's build artifacts
#
# Wave gating: every `-waves` variant just re-invokes the underlying
# target with WAVES=1 in the environment. Mirrors the convention used
# in val/{common,amba,integ_*} and the other components/dv/tests/Makefiles.
# ==============================================================================

SHELL := /bin/bash

ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

SUBDIRS := fub

.DEFAULT_GOAL := help

.PHONY: help
help:
	@echo "================================================================================"
	@echo "Misc dv/tests umbrella"
	@echo "================================================================================"
	@echo "  make run-fub                    Run all FUB tests"
	@echo "  make run-fub-waves              Same with WAVES=1"
	@echo "  make run-fub-parallel           FUB tests in parallel"
	@echo "  make run-fub-parallel-waves     FUB parallel tests with waves"
	@echo "  make clean-all                  Clean every subdir's build artifacts"
	@echo ""
	@echo "  make fub-<target>               Forward arbitrary <target> to fub/Makefile"
	@echo "  make fub-<target>-waves         Same with WAVES=1"
	@echo "================================================================================"

# Top-level shortcuts that map to the canonical recipe in each subdir.
.PHONY: run-fub run-fub-parallel
run-fub:
	@$(MAKE) --no-print-directory -C fub run-all
run-fub-parallel:
	@$(MAKE) --no-print-directory -C fub run-all-parallel

# Generic delegation: `make fub-<anything>` runs `<anything>` inside fub/.
# Combined with the `%-waves` pattern below, you get every fub/ target's
# wave variant for free, e.g. `make fub-run-all-gate-waves`.
fub-%:
	@$(MAKE) --no-print-directory -C fub $*

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
