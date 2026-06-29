# ==============================================================================
# ddr2_char_macro test runner
# ==============================================================================

SHELL := /bin/bash

ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

PYTEST = python3 -m pytest

.PHONY: help
help:
	@echo "macro test targets:"
	@echo "  make run            Run macro suite (all shapes)"
	@echo "  make run-smoke      Run smoke shapes only (1x1, 1x2, 2x1, 2x2)"
	@echo "  make run-<shape>    Run one shape (smoke, smoke_1x2, kb1, kb4, kb32, ...)"
	@echo "  make clean          Wipe local_sim_build + logs + pycache"
	@echo "  make clean-all      clean + every wave / trace / log artifact"

.PHONY: run
run:
	$(PYTEST) test_ddr2_char_macro.py -v --tb=short

.PHONY: run-smoke
run-smoke:
	$(PYTEST) test_ddr2_char_macro.py -k "smoke" -v --tb=short

run-%:
	$(PYTEST) "test_ddr2_char_macro.py::test_ddr2_char_macro[$*]" -v --tb=short

.PHONY: clean
clean:
	@echo "Cleaning local artifacts..."
	rm -rf __pycache__ .pytest_cache *.pyc
	rm -rf local_sim_build logs
	find . -name '*.pyc' -delete

.PHONY: clean-all
clean-all: clean
	@echo "Cleaning all test artifacts..."
	find . -name "*.vcd" -delete
	find . -name "*.fst" -delete
	find . -name "*.fst.hier" -delete
	find . -name "*.log" -delete
