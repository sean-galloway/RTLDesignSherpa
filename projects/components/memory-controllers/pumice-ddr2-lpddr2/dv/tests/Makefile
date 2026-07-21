# ==============================================================================
# pumice-ddr2-lpddr2 dv/tests Umbrella Makefile
# ==============================================================================
#
# Unifying wrapper over the per-tier sub-Makefiles (fub/, macro/, top/) so this
# component exposes the same run-all-<gate|func|full>[-parallel] interface as the
# other components (see projects/components/Makefile).
#
# The tiers run SERIALLY (fub -> macro -> top); the -parallel variants use each
# tier's parallel (-n workers) target internally.
#
# PREREQUISITES:
#   source $REPO_ROOT/env_python
# ==============================================================================

SHELL := /bin/bash

ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

# Tier order matters -- run serially in this sequence.
SUBDIRS := fub macro top

.DEFAULT_GOAL := help

.PHONY: help
help:
	@echo "================================================================================"
	@echo "pumice-ddr2-lpddr2 dv/tests umbrella (tiers: $(SUBDIRS))"
	@echo "================================================================================"
	@echo "  make run-all[-parallel]                Run every tier (default level)"
	@echo "  make run-all-<gate|func|full>[-parallel]  Run every tier at that level"
	@echo "  make clean-all                         Clean every tier's build artifacts"
	@echo ""
	@echo "  Tiers run serially fub -> macro -> top; -parallel uses each tier's -n workers."
	@echo "================================================================================"

# Serial tier fan-out.  $(1) = the per-tier target to invoke in each subdir.
define RUN_TIERS
	@for d in $(SUBDIRS); do \
	    echo "==> $$d ($(1))"; \
	    $(MAKE) --no-print-directory -C $$d $(1) || exit 1; \
	done
endef

.PHONY: run-all run-all-parallel
run-all:               ; $(call RUN_TIERS,run-all)
run-all-parallel:      ; $(call RUN_TIERS,run-all-parallel)

.PHONY: run-all-gate run-all-gate-parallel
run-all-gate:          ; $(call RUN_TIERS,run-gate)
run-all-gate-parallel: ; $(call RUN_TIERS,run-gate-parallel)

.PHONY: run-all-func run-all-func-parallel
run-all-func:          ; $(call RUN_TIERS,run-func)
run-all-func-parallel: ; $(call RUN_TIERS,run-func-parallel)

.PHONY: run-all-full run-all-full-parallel
run-all-full:          ; $(call RUN_TIERS,run-full)
run-all-full-parallel: ; $(call RUN_TIERS,run-full-parallel)

.PHONY: clean-all
clean-all:
	@for d in $(SUBDIRS); do \
	    echo "[clean-all] $$d/"; \
	    $(MAKE) --no-print-directory -C $$d clean-all 2>/dev/null || true; \
	done
