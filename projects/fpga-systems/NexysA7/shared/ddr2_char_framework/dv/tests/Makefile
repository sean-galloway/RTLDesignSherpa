# ==============================================================================
# ddr2_char_macro test runner
# ==============================================================================

SHELL := /bin/bash

ifndef REPO_ROOT
$(error REPO_ROOT is not set. Please run: source $$REPO_ROOT/env_python)
endif

PYTEST         = python3 -m pytest
PYTEST_VERBOSE = -v
PYTEST_TBSTYLE = --tb=short
# 48 parallel workers to match the components-side Makefiles.
PYTEST_XDIST   = -n 48
PYTEST_RERUNS  = --reruns 3 --reruns-delay 1
# `.` so pytest auto-discovers every test_*.py file in this dir — right
# now that's just test_ddr2_char_macro.py, but future additions get
# picked up automatically instead of silently being skipped.
ALL_TESTS      = .

.PHONY: help
help:
	@echo "macro test targets:"
	@echo "  make run                          Run macro suite (all shapes)"
	@echo "  make run-smoke                    Run smoke shapes only"
	@echo "  make run-<shape>                  Run one shape (smoke, smoke_1x2, kb1, kb4, kb32, ...)"
	@echo ""
	@echo "PARALLEL SWEEPS (xdist + reruns):"
	@echo "  make run-gate-parallel            GATE + xdist + reruns"
	@echo "  make run-gate-parallel-waves      GATE + xdist + reruns + waves"
	@echo "  make run-func-parallel            FUNC + xdist + reruns"
	@echo "  make run-func-parallel-waves      FUNC + xdist + reruns + waves"
	@echo "  make run-full-parallel            FULL + xdist + reruns"
	@echo "  make run-full-parallel-waves      FULL + xdist + reruns + waves"
	@echo ""
	@echo "  make clean                        Wipe local_sim_build + logs + pycache"
	@echo "  make clean-all                    clean + every wave / trace / log artifact"

.PHONY: run
run:
	$(PYTEST) test_ddr2_char_macro.py -v --tb=short

.PHONY: run-smoke
run-smoke:
	$(PYTEST) test_ddr2_char_macro.py -k "smoke" -v --tb=short

run-%:
	$(PYTEST) "test_ddr2_char_macro.py::test_ddr2_char_macro[$*]" -v --tb=short

# ==============================================================================
# Parallel test-level sweeps (mirror memctrl fub/macro Makefiles)
# ==============================================================================

.PHONY: run-gate-parallel
run-gate-parallel:
	TEST_LEVEL=GATE $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-gate-parallel-waves
run-gate-parallel-waves:
	WAVES=1 TEST_LEVEL=GATE $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-func-parallel
run-func-parallel:
	TEST_LEVEL=FUNC $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-func-parallel-waves
run-func-parallel-waves:
	WAVES=1 TEST_LEVEL=FUNC $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-full-parallel
run-full-parallel:
	TEST_LEVEL=FULL $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

.PHONY: run-full-parallel-waves
run-full-parallel-waves:
	WAVES=1 TEST_LEVEL=FULL $(PYTEST) $(ALL_TESTS) $(PYTEST_VERBOSE) $(PYTEST_TBSTYLE) $(PYTEST_XDIST) $(PYTEST_RERUNS)

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
