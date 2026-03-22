# ==============================================================================
# AUTO-GENERATED — do not edit manually
# Regenerate: python3 bin/generate_test_targets.py
# Source:     test_environments.toml
# ==============================================================================

PYTEST ?= python3 -m pytest

# --- val-common: RTL common modules (counters, arbiters, FIFOs, math, etc.) ---

.PHONY: test-val-common
test-val-common:
	@echo "=== val-common FUNC (parallel) ==="
	@cd val/common && REG_LEVEL=FUNC $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-common-gate
test-val-common-gate:
	@echo "=== val-common GATE (parallel) ==="
	@cd val/common && REG_LEVEL=GATE $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-common-func
test-val-common-func:
	@echo "=== val-common FUNC (parallel) ==="
	@cd val/common && REG_LEVEL=FUNC $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-common-full
test-val-common-full:
	@echo "=== val-common FULL (parallel) ==="
	@cd val/common && REG_LEVEL=FULL $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-common-gate-waves
test-val-common-gate-waves:
	@echo "=== val-common GATE (parallel + waves) ==="
	@cd val/common && REG_LEVEL=GATE WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-common-func-waves
test-val-common-func-waves:
	@echo "=== val-common FUNC (parallel + waves) ==="
	@cd val/common && REG_LEVEL=FUNC WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-common-full-waves
test-val-common-full-waves:
	@echo "=== val-common FULL (parallel + waves) ==="
	@cd val/common && REG_LEVEL=FULL WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-common-gate-serial
test-val-common-gate-serial:
	@echo "=== val-common GATE (serial) ==="
	@cd val/common && REG_LEVEL=GATE $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-common-func-serial
test-val-common-func-serial:
	@echo "=== val-common FUNC (serial) ==="
	@cd val/common && REG_LEVEL=FUNC $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-common-full-serial
test-val-common-full-serial:
	@echo "=== val-common FULL (serial) ==="
	@cd val/common && REG_LEVEL=FULL $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: coverage-val-common
coverage-val-common:
	@echo "=== val-common FUNC (parallel + coverage) ==="
	@cd val/common && REG_LEVEL=FUNC COVERAGE=1 $(PYTEST) -v --tb=short -n 24 --reruns 5 --reruns-delay 2 test_*.py

# --- val-amba: AMBA protocol modules (AXI4, APB, AXIS monitors) ---

.PHONY: test-val-amba
test-val-amba:
	@echo "=== val-amba FUNC (parallel) ==="
	@cd val/amba && REG_LEVEL=FUNC $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-amba-gate
test-val-amba-gate:
	@echo "=== val-amba GATE (parallel) ==="
	@cd val/amba && REG_LEVEL=GATE $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-amba-func
test-val-amba-func:
	@echo "=== val-amba FUNC (parallel) ==="
	@cd val/amba && REG_LEVEL=FUNC $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-amba-full
test-val-amba-full:
	@echo "=== val-amba FULL (parallel) ==="
	@cd val/amba && REG_LEVEL=FULL $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-amba-gate-waves
test-val-amba-gate-waves:
	@echo "=== val-amba GATE (parallel + waves) ==="
	@cd val/amba && REG_LEVEL=GATE WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-amba-func-waves
test-val-amba-func-waves:
	@echo "=== val-amba FUNC (parallel + waves) ==="
	@cd val/amba && REG_LEVEL=FUNC WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-amba-full-waves
test-val-amba-full-waves:
	@echo "=== val-amba FULL (parallel + waves) ==="
	@cd val/amba && REG_LEVEL=FULL WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-amba-gate-serial
test-val-amba-gate-serial:
	@echo "=== val-amba GATE (serial) ==="
	@cd val/amba && REG_LEVEL=GATE $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-amba-func-serial
test-val-amba-func-serial:
	@echo "=== val-amba FUNC (serial) ==="
	@cd val/amba && REG_LEVEL=FUNC $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-amba-full-serial
test-val-amba-full-serial:
	@echo "=== val-amba FULL (serial) ==="
	@cd val/amba && REG_LEVEL=FULL $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: coverage-val-amba
coverage-val-amba:
	@echo "=== val-amba FUNC (parallel + coverage) ==="
	@cd val/amba && REG_LEVEL=FUNC COVERAGE=1 $(PYTEST) -v --tb=short -n 24 --reruns 5 --reruns-delay 2 test_*.py

# --- val-integ-common: Integration tests for common modules ---

.PHONY: test-val-integ-common
test-val-integ-common:
	@echo "=== val-integ-common FUNC (parallel) ==="
	@cd val/integ_common && REG_LEVEL=FUNC $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-integ-common-gate
test-val-integ-common-gate:
	@echo "=== val-integ-common GATE (parallel) ==="
	@cd val/integ_common && REG_LEVEL=GATE $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-integ-common-func
test-val-integ-common-func:
	@echo "=== val-integ-common FUNC (parallel) ==="
	@cd val/integ_common && REG_LEVEL=FUNC $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-integ-common-full
test-val-integ-common-full:
	@echo "=== val-integ-common FULL (parallel) ==="
	@cd val/integ_common && REG_LEVEL=FULL $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-integ-common-gate-waves
test-val-integ-common-gate-waves:
	@echo "=== val-integ-common GATE (parallel + waves) ==="
	@cd val/integ_common && REG_LEVEL=GATE WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-integ-common-func-waves
test-val-integ-common-func-waves:
	@echo "=== val-integ-common FUNC (parallel + waves) ==="
	@cd val/integ_common && REG_LEVEL=FUNC WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-integ-common-full-waves
test-val-integ-common-full-waves:
	@echo "=== val-integ-common FULL (parallel + waves) ==="
	@cd val/integ_common && REG_LEVEL=FULL WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-integ-common-gate-serial
test-val-integ-common-gate-serial:
	@echo "=== val-integ-common GATE (serial) ==="
	@cd val/integ_common && REG_LEVEL=GATE $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-integ-common-func-serial
test-val-integ-common-func-serial:
	@echo "=== val-integ-common FUNC (serial) ==="
	@cd val/integ_common && REG_LEVEL=FUNC $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-integ-common-full-serial
test-val-integ-common-full-serial:
	@echo "=== val-integ-common FULL (serial) ==="
	@cd val/integ_common && REG_LEVEL=FULL $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: coverage-val-integ-common
coverage-val-integ-common:
	@echo "=== val-integ-common FUNC (parallel + coverage) ==="
	@cd val/integ_common && REG_LEVEL=FUNC COVERAGE=1 $(PYTEST) -v --tb=short -n 24 --reruns 5 --reruns-delay 2 test_*.py

# --- val-integ-amba: Integration tests for AMBA modules ---

.PHONY: test-val-integ-amba
test-val-integ-amba:
	@echo "=== val-integ-amba FUNC (parallel) ==="
	@cd val/integ_amba && REG_LEVEL=FUNC $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-integ-amba-gate
test-val-integ-amba-gate:
	@echo "=== val-integ-amba GATE (parallel) ==="
	@cd val/integ_amba && REG_LEVEL=GATE $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-integ-amba-func
test-val-integ-amba-func:
	@echo "=== val-integ-amba FUNC (parallel) ==="
	@cd val/integ_amba && REG_LEVEL=FUNC $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-integ-amba-full
test-val-integ-amba-full:
	@echo "=== val-integ-amba FULL (parallel) ==="
	@cd val/integ_amba && REG_LEVEL=FULL $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-integ-amba-gate-waves
test-val-integ-amba-gate-waves:
	@echo "=== val-integ-amba GATE (parallel + waves) ==="
	@cd val/integ_amba && REG_LEVEL=GATE WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-integ-amba-func-waves
test-val-integ-amba-func-waves:
	@echo "=== val-integ-amba FUNC (parallel + waves) ==="
	@cd val/integ_amba && REG_LEVEL=FUNC WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-integ-amba-full-waves
test-val-integ-amba-full-waves:
	@echo "=== val-integ-amba FULL (parallel + waves) ==="
	@cd val/integ_amba && REG_LEVEL=FULL WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-integ-amba-gate-serial
test-val-integ-amba-gate-serial:
	@echo "=== val-integ-amba GATE (serial) ==="
	@cd val/integ_amba && REG_LEVEL=GATE $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-integ-amba-func-serial
test-val-integ-amba-func-serial:
	@echo "=== val-integ-amba FUNC (serial) ==="
	@cd val/integ_amba && REG_LEVEL=FUNC $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-val-integ-amba-full-serial
test-val-integ-amba-full-serial:
	@echo "=== val-integ-amba FULL (serial) ==="
	@cd val/integ_amba && REG_LEVEL=FULL $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: coverage-val-integ-amba
coverage-val-integ-amba:
	@echo "=== val-integ-amba FUNC (parallel + coverage) ==="
	@cd val/integ_amba && REG_LEVEL=FUNC COVERAGE=1 $(PYTEST) -v --tb=short -n 24 --reruns 5 --reruns-delay 2 test_*.py

# --- stream: STREAM scatter-gather DMA engine ---

.PHONY: test-stream
test-stream:
	@echo "=== stream FUNC (parallel) ==="
	@cd projects/components/stream/dv/tests && TEST_LEVEL=func $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-stream-gate
test-stream-gate:
	@echo "=== stream GATE (parallel) ==="
	@cd projects/components/stream/dv/tests && TEST_LEVEL=gate $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-stream-func
test-stream-func:
	@echo "=== stream FUNC (parallel) ==="
	@cd projects/components/stream/dv/tests && TEST_LEVEL=func $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-stream-full
test-stream-full:
	@echo "=== stream FULL (parallel) ==="
	@cd projects/components/stream/dv/tests && TEST_LEVEL=full $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-stream-gate-waves
test-stream-gate-waves:
	@echo "=== stream GATE (parallel + waves) ==="
	@cd projects/components/stream/dv/tests && TEST_LEVEL=gate WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-stream-func-waves
test-stream-func-waves:
	@echo "=== stream FUNC (parallel + waves) ==="
	@cd projects/components/stream/dv/tests && TEST_LEVEL=func WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-stream-full-waves
test-stream-full-waves:
	@echo "=== stream FULL (parallel + waves) ==="
	@cd projects/components/stream/dv/tests && TEST_LEVEL=full WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-stream-gate-serial
test-stream-gate-serial:
	@echo "=== stream GATE (serial) ==="
	@cd projects/components/stream/dv/tests && TEST_LEVEL=gate $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-stream-func-serial
test-stream-func-serial:
	@echo "=== stream FUNC (serial) ==="
	@cd projects/components/stream/dv/tests && TEST_LEVEL=func $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-stream-full-serial
test-stream-full-serial:
	@echo "=== stream FULL (serial) ==="
	@cd projects/components/stream/dv/tests && TEST_LEVEL=full $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: coverage-stream
coverage-stream:
	@echo "=== stream coverage ==="
	@$(MAKE) -C projects/components/stream/dv/tests fresh-coverage

.PHONY: coverage-report-stream
coverage-report-stream:
	@echo "=== stream coverage report ==="
	@$(MAKE) -C projects/components/stream/dv/tests coverage-report

# --- rapids: RAPIDS descriptor-driven accelerator ---

.PHONY: test-rapids
test-rapids:
	@echo "=== rapids FUNC (parallel) ==="
	@cd projects/components/rapids/dv/tests && REG_LEVEL=FUNC $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-rapids-gate
test-rapids-gate:
	@echo "=== rapids GATE (parallel) ==="
	@cd projects/components/rapids/dv/tests && REG_LEVEL=GATE $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-rapids-func
test-rapids-func:
	@echo "=== rapids FUNC (parallel) ==="
	@cd projects/components/rapids/dv/tests && REG_LEVEL=FUNC $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-rapids-full
test-rapids-full:
	@echo "=== rapids FULL (parallel) ==="
	@cd projects/components/rapids/dv/tests && REG_LEVEL=FULL $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-rapids-gate-waves
test-rapids-gate-waves:
	@echo "=== rapids GATE (parallel + waves) ==="
	@cd projects/components/rapids/dv/tests && REG_LEVEL=GATE WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-rapids-func-waves
test-rapids-func-waves:
	@echo "=== rapids FUNC (parallel + waves) ==="
	@cd projects/components/rapids/dv/tests && REG_LEVEL=FUNC WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-rapids-full-waves
test-rapids-full-waves:
	@echo "=== rapids FULL (parallel + waves) ==="
	@cd projects/components/rapids/dv/tests && REG_LEVEL=FULL WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-rapids-gate-serial
test-rapids-gate-serial:
	@echo "=== rapids GATE (serial) ==="
	@cd projects/components/rapids/dv/tests && REG_LEVEL=GATE $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-rapids-func-serial
test-rapids-func-serial:
	@echo "=== rapids FUNC (serial) ==="
	@cd projects/components/rapids/dv/tests && REG_LEVEL=FUNC $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-rapids-full-serial
test-rapids-full-serial:
	@echo "=== rapids FULL (serial) ==="
	@cd projects/components/rapids/dv/tests && REG_LEVEL=FULL $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: coverage-rapids
coverage-rapids:
	@echo "=== rapids coverage ==="
	@$(MAKE) -C projects/components/rapids/dv/tests coverage-full-report

.PHONY: coverage-report-rapids
coverage-report-rapids:
	@echo "=== rapids coverage report ==="
	@$(MAKE) -C projects/components/rapids/dv/tests coverage-report

# --- bridge: AXI4 crossbar bridge (sequential only — ~1GB per test) ---

.PHONY: test-bridge
test-bridge:
	@echo "=== bridge FUNC (serial) ==="
	@cd projects/components/bridge/dv/tests && REG_LEVEL=FUNC $(PYTEST) -v --tb=short test_*.py

.PHONY: test-bridge-gate
test-bridge-gate:
	@echo "=== bridge GATE (serial) ==="
	@cd projects/components/bridge/dv/tests && REG_LEVEL=GATE $(PYTEST) -v --tb=short test_*.py

.PHONY: test-bridge-func
test-bridge-func:
	@echo "=== bridge FUNC (serial) ==="
	@cd projects/components/bridge/dv/tests && REG_LEVEL=FUNC $(PYTEST) -v --tb=short test_*.py

.PHONY: test-bridge-full
test-bridge-full:
	@echo "=== bridge FULL (serial) ==="
	@cd projects/components/bridge/dv/tests && REG_LEVEL=FULL $(PYTEST) -v --tb=short test_*.py

.PHONY: test-bridge-gate-waves
test-bridge-gate-waves:
	@echo "=== bridge GATE (serial + waves) ==="
	@cd projects/components/bridge/dv/tests && REG_LEVEL=GATE WAVES=1 $(PYTEST) -v --tb=short test_*.py

.PHONY: test-bridge-func-waves
test-bridge-func-waves:
	@echo "=== bridge FUNC (serial + waves) ==="
	@cd projects/components/bridge/dv/tests && REG_LEVEL=FUNC WAVES=1 $(PYTEST) -v --tb=short test_*.py

.PHONY: test-bridge-full-waves
test-bridge-full-waves:
	@echo "=== bridge FULL (serial + waves) ==="
	@cd projects/components/bridge/dv/tests && REG_LEVEL=FULL WAVES=1 $(PYTEST) -v --tb=short test_*.py

.PHONY: test-bridge-gate-serial
test-bridge-gate-serial:
	@echo "=== bridge GATE (serial) ==="
	@cd projects/components/bridge/dv/tests && REG_LEVEL=GATE $(PYTEST) -v --tb=short test_*.py

.PHONY: test-bridge-func-serial
test-bridge-func-serial:
	@echo "=== bridge FUNC (serial) ==="
	@cd projects/components/bridge/dv/tests && REG_LEVEL=FUNC $(PYTEST) -v --tb=short test_*.py

.PHONY: test-bridge-full-serial
test-bridge-full-serial:
	@echo "=== bridge FULL (serial) ==="
	@cd projects/components/bridge/dv/tests && REG_LEVEL=FULL $(PYTEST) -v --tb=short test_*.py

.PHONY: coverage-bridge
coverage-bridge:
	@echo "=== bridge coverage ==="
	@$(MAKE) -C projects/components/bridge/dv/tests fresh-coverage

.PHONY: coverage-report-bridge
coverage-report-bridge:
	@echo "=== bridge coverage report ==="
	@$(MAKE) -C projects/components/bridge/dv/tests coverage-report

# --- converters: Data width and protocol converters ---

.PHONY: test-converters
test-converters:
	@echo "=== converters FUNC (parallel) ==="
	@cd projects/components/converters/dv/tests && REG_LEVEL=FUNC $(PYTEST) -v --tb=short -n 48 test_*.py

.PHONY: test-converters-gate
test-converters-gate:
	@echo "=== converters GATE (parallel) ==="
	@cd projects/components/converters/dv/tests && REG_LEVEL=GATE $(PYTEST) -v --tb=short -n 48 test_*.py

.PHONY: test-converters-func
test-converters-func:
	@echo "=== converters FUNC (parallel) ==="
	@cd projects/components/converters/dv/tests && REG_LEVEL=FUNC $(PYTEST) -v --tb=short -n 48 test_*.py

.PHONY: test-converters-full
test-converters-full:
	@echo "=== converters FULL (parallel) ==="
	@cd projects/components/converters/dv/tests && REG_LEVEL=FULL $(PYTEST) -v --tb=short -n 48 test_*.py

.PHONY: test-converters-gate-waves
test-converters-gate-waves:
	@echo "=== converters GATE (parallel + waves) ==="
	@cd projects/components/converters/dv/tests && REG_LEVEL=GATE WAVES=1 $(PYTEST) -v --tb=short -n 48 test_*.py

.PHONY: test-converters-func-waves
test-converters-func-waves:
	@echo "=== converters FUNC (parallel + waves) ==="
	@cd projects/components/converters/dv/tests && REG_LEVEL=FUNC WAVES=1 $(PYTEST) -v --tb=short -n 48 test_*.py

.PHONY: test-converters-full-waves
test-converters-full-waves:
	@echo "=== converters FULL (parallel + waves) ==="
	@cd projects/components/converters/dv/tests && REG_LEVEL=FULL WAVES=1 $(PYTEST) -v --tb=short -n 48 test_*.py

.PHONY: test-converters-gate-serial
test-converters-gate-serial:
	@echo "=== converters GATE (serial) ==="
	@cd projects/components/converters/dv/tests && REG_LEVEL=GATE $(PYTEST) -v --tb=short test_*.py

.PHONY: test-converters-func-serial
test-converters-func-serial:
	@echo "=== converters FUNC (serial) ==="
	@cd projects/components/converters/dv/tests && REG_LEVEL=FUNC $(PYTEST) -v --tb=short test_*.py

.PHONY: test-converters-full-serial
test-converters-full-serial:
	@echo "=== converters FULL (serial) ==="
	@cd projects/components/converters/dv/tests && REG_LEVEL=FULL $(PYTEST) -v --tb=short test_*.py

.PHONY: coverage-converters
coverage-converters:
	@echo "=== converters coverage ==="
	@$(MAKE) -C projects/components/converters/dv/tests fresh-coverage

.PHONY: coverage-report-converters
coverage-report-converters:
	@echo "=== converters coverage report ==="
	@$(MAKE) -C projects/components/converters/dv/tests coverage-report

# --- apb-xbar: APB crossbar ---

.PHONY: test-apb-xbar
test-apb-xbar:
	@echo "=== apb-xbar FUNC (parallel) ==="
	@cd projects/components/apb_xbar/dv/tests && REG_LEVEL=FUNC $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-apb-xbar-gate
test-apb-xbar-gate:
	@echo "=== apb-xbar GATE (parallel) ==="
	@cd projects/components/apb_xbar/dv/tests && REG_LEVEL=GATE $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-apb-xbar-func
test-apb-xbar-func:
	@echo "=== apb-xbar FUNC (parallel) ==="
	@cd projects/components/apb_xbar/dv/tests && REG_LEVEL=FUNC $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-apb-xbar-full
test-apb-xbar-full:
	@echo "=== apb-xbar FULL (parallel) ==="
	@cd projects/components/apb_xbar/dv/tests && REG_LEVEL=FULL $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-apb-xbar-gate-waves
test-apb-xbar-gate-waves:
	@echo "=== apb-xbar GATE (parallel + waves) ==="
	@cd projects/components/apb_xbar/dv/tests && REG_LEVEL=GATE WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-apb-xbar-func-waves
test-apb-xbar-func-waves:
	@echo "=== apb-xbar FUNC (parallel + waves) ==="
	@cd projects/components/apb_xbar/dv/tests && REG_LEVEL=FUNC WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-apb-xbar-full-waves
test-apb-xbar-full-waves:
	@echo "=== apb-xbar FULL (parallel + waves) ==="
	@cd projects/components/apb_xbar/dv/tests && REG_LEVEL=FULL WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-apb-xbar-gate-serial
test-apb-xbar-gate-serial:
	@echo "=== apb-xbar GATE (serial) ==="
	@cd projects/components/apb_xbar/dv/tests && REG_LEVEL=GATE $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-apb-xbar-func-serial
test-apb-xbar-func-serial:
	@echo "=== apb-xbar FUNC (serial) ==="
	@cd projects/components/apb_xbar/dv/tests && REG_LEVEL=FUNC $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-apb-xbar-full-serial
test-apb-xbar-full-serial:
	@echo "=== apb-xbar FULL (serial) ==="
	@cd projects/components/apb_xbar/dv/tests && REG_LEVEL=FULL $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: coverage-apb-xbar
coverage-apb-xbar:
	@echo "=== apb-xbar FUNC (parallel + coverage) ==="
	@cd projects/components/apb_xbar/dv/tests && REG_LEVEL=FUNC COVERAGE=1 $(PYTEST) -v --tb=short -n 24 --reruns 5 --reruns-delay 2 test_*.py

# --- retro-legacy: Retro legacy blocks ---

.PHONY: test-retro-legacy
test-retro-legacy:
	@echo "=== retro-legacy FUNC (parallel) ==="
	@cd projects/components/retro_legacy_blocks/dv/tests && REG_LEVEL=FUNC $(PYTEST) -v --tb=short -n 48 test_*.py

.PHONY: test-retro-legacy-gate
test-retro-legacy-gate:
	@echo "=== retro-legacy GATE (parallel) ==="
	@cd projects/components/retro_legacy_blocks/dv/tests && REG_LEVEL=GATE $(PYTEST) -v --tb=short -n 48 test_*.py

.PHONY: test-retro-legacy-func
test-retro-legacy-func:
	@echo "=== retro-legacy FUNC (parallel) ==="
	@cd projects/components/retro_legacy_blocks/dv/tests && REG_LEVEL=FUNC $(PYTEST) -v --tb=short -n 48 test_*.py

.PHONY: test-retro-legacy-full
test-retro-legacy-full:
	@echo "=== retro-legacy FULL (parallel) ==="
	@cd projects/components/retro_legacy_blocks/dv/tests && REG_LEVEL=FULL $(PYTEST) -v --tb=short -n 48 test_*.py

.PHONY: test-retro-legacy-gate-waves
test-retro-legacy-gate-waves:
	@echo "=== retro-legacy GATE (parallel + waves) ==="
	@cd projects/components/retro_legacy_blocks/dv/tests && REG_LEVEL=GATE WAVES=1 $(PYTEST) -v --tb=short -n 48 test_*.py

.PHONY: test-retro-legacy-func-waves
test-retro-legacy-func-waves:
	@echo "=== retro-legacy FUNC (parallel + waves) ==="
	@cd projects/components/retro_legacy_blocks/dv/tests && REG_LEVEL=FUNC WAVES=1 $(PYTEST) -v --tb=short -n 48 test_*.py

.PHONY: test-retro-legacy-full-waves
test-retro-legacy-full-waves:
	@echo "=== retro-legacy FULL (parallel + waves) ==="
	@cd projects/components/retro_legacy_blocks/dv/tests && REG_LEVEL=FULL WAVES=1 $(PYTEST) -v --tb=short -n 48 test_*.py

.PHONY: test-retro-legacy-gate-serial
test-retro-legacy-gate-serial:
	@echo "=== retro-legacy GATE (serial) ==="
	@cd projects/components/retro_legacy_blocks/dv/tests && REG_LEVEL=GATE $(PYTEST) -v --tb=short test_*.py

.PHONY: test-retro-legacy-func-serial
test-retro-legacy-func-serial:
	@echo "=== retro-legacy FUNC (serial) ==="
	@cd projects/components/retro_legacy_blocks/dv/tests && REG_LEVEL=FUNC $(PYTEST) -v --tb=short test_*.py

.PHONY: test-retro-legacy-full-serial
test-retro-legacy-full-serial:
	@echo "=== retro-legacy FULL (serial) ==="
	@cd projects/components/retro_legacy_blocks/dv/tests && REG_LEVEL=FULL $(PYTEST) -v --tb=short test_*.py

# --- timing-char: Timing characterization ---

.PHONY: test-timing-char
test-timing-char:
	@echo "=== timing-char FUNC (parallel) ==="
	@cd projects/components/timing_characterization/dv/tests && REG_LEVEL=FUNC $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-timing-char-gate
test-timing-char-gate:
	@echo "=== timing-char GATE (parallel) ==="
	@cd projects/components/timing_characterization/dv/tests && REG_LEVEL=GATE $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-timing-char-func
test-timing-char-func:
	@echo "=== timing-char FUNC (parallel) ==="
	@cd projects/components/timing_characterization/dv/tests && REG_LEVEL=FUNC $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-timing-char-full
test-timing-char-full:
	@echo "=== timing-char FULL (parallel) ==="
	@cd projects/components/timing_characterization/dv/tests && REG_LEVEL=FULL $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-timing-char-gate-waves
test-timing-char-gate-waves:
	@echo "=== timing-char GATE (parallel + waves) ==="
	@cd projects/components/timing_characterization/dv/tests && REG_LEVEL=GATE WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-timing-char-func-waves
test-timing-char-func-waves:
	@echo "=== timing-char FUNC (parallel + waves) ==="
	@cd projects/components/timing_characterization/dv/tests && REG_LEVEL=FUNC WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-timing-char-full-waves
test-timing-char-full-waves:
	@echo "=== timing-char FULL (parallel + waves) ==="
	@cd projects/components/timing_characterization/dv/tests && REG_LEVEL=FULL WAVES=1 $(PYTEST) -v --tb=short -n 48 --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-timing-char-gate-serial
test-timing-char-gate-serial:
	@echo "=== timing-char GATE (serial) ==="
	@cd projects/components/timing_characterization/dv/tests && REG_LEVEL=GATE $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-timing-char-func-serial
test-timing-char-func-serial:
	@echo "=== timing-char FUNC (serial) ==="
	@cd projects/components/timing_characterization/dv/tests && REG_LEVEL=FUNC $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

.PHONY: test-timing-char-full-serial
test-timing-char-full-serial:
	@echo "=== timing-char FULL (serial) ==="
	@cd projects/components/timing_characterization/dv/tests && REG_LEVEL=FULL $(PYTEST) -v --tb=short --reruns 3 --reruns-delay 1 test_*.py

# ==============================================================================
# Aggregate targets — all environments
# ==============================================================================

.PHONY: test-all-gate
test-all-gate: test-val-common-gate test-val-amba-gate test-val-integ-common-gate test-val-integ-amba-gate test-stream-gate test-rapids-gate test-bridge-gate test-converters-gate test-apb-xbar-gate test-retro-legacy-gate test-timing-char-gate

.PHONY: test-all-func
test-all-func: test-val-common-func test-val-amba-func test-val-integ-common-func test-val-integ-amba-func test-stream-func test-rapids-func test-bridge-func test-converters-func test-apb-xbar-func test-retro-legacy-func test-timing-char-func

.PHONY: test-all-full
test-all-full: test-val-common-full test-val-amba-full test-val-integ-common-full test-val-integ-amba-full test-stream-full test-rapids-full test-bridge-full test-converters-full test-apb-xbar-full test-retro-legacy-full test-timing-char-full

.PHONY: test-all-gate-serial
test-all-gate-serial: test-val-common-gate-serial test-val-amba-gate-serial test-val-integ-common-gate-serial test-val-integ-amba-gate-serial test-stream-gate-serial test-rapids-gate-serial test-bridge-gate-serial test-converters-gate-serial test-apb-xbar-gate-serial test-retro-legacy-gate-serial test-timing-char-gate-serial

.PHONY: test-all-func-serial
test-all-func-serial: test-val-common-func-serial test-val-amba-func-serial test-val-integ-common-func-serial test-val-integ-amba-func-serial test-stream-func-serial test-rapids-func-serial test-bridge-func-serial test-converters-func-serial test-apb-xbar-func-serial test-retro-legacy-func-serial test-timing-char-func-serial

.PHONY: test-all-full-serial
test-all-full-serial: test-val-common-full-serial test-val-amba-full-serial test-val-integ-common-full-serial test-val-integ-amba-full-serial test-stream-full-serial test-rapids-full-serial test-bridge-full-serial test-converters-full-serial test-apb-xbar-full-serial test-retro-legacy-full-serial test-timing-char-full-serial

.PHONY: test-all-gate-waves
test-all-gate-waves: test-val-common-gate-waves test-val-amba-gate-waves test-val-integ-common-gate-waves test-val-integ-amba-gate-waves test-stream-gate-waves test-rapids-gate-waves test-bridge-gate-waves test-converters-gate-waves test-apb-xbar-gate-waves test-retro-legacy-gate-waves test-timing-char-gate-waves

.PHONY: test-all-func-waves
test-all-func-waves: test-val-common-func-waves test-val-amba-func-waves test-val-integ-common-func-waves test-val-integ-amba-func-waves test-stream-func-waves test-rapids-func-waves test-bridge-func-waves test-converters-func-waves test-apb-xbar-func-waves test-retro-legacy-func-waves test-timing-char-func-waves

.PHONY: test-all-full-waves
test-all-full-waves: test-val-common-full-waves test-val-amba-full-waves test-val-integ-common-full-waves test-val-integ-amba-full-waves test-stream-full-waves test-rapids-full-waves test-bridge-full-waves test-converters-full-waves test-apb-xbar-full-waves test-retro-legacy-full-waves test-timing-char-full-waves

.PHONY: coverage-all
coverage-all: coverage-val-common coverage-val-amba coverage-val-integ-common coverage-val-integ-amba coverage-stream coverage-rapids coverage-bridge coverage-converters coverage-apb-xbar

.PHONY: coverage-report-all
coverage-report-all: coverage-report-stream coverage-report-rapids coverage-report-bridge coverage-report-converters

# ==============================================================================
# Help for generated targets
# ==============================================================================

.PHONY: help-envs
help-envs:
	@echo "================================================================================"
	@echo "Test Environment Targets (generated from test_environments.toml)"
	@echo "================================================================================"
	@echo ""
	@echo "DEFAULT (FUNC, parallel):"
	@echo "  make test-val-common                   RTL common modules (counters, arbiters, FIFOs, math, etc.) (48w)"
	@echo "  make test-val-amba                     AMBA protocol modules (AXI4, APB, AXIS monitors) (48w)"
	@echo "  make test-val-integ-common             Integration tests for common modules (48w)"
	@echo "  make test-val-integ-amba               Integration tests for AMBA modules (48w)"
	@echo "  make test-stream                       STREAM scatter-gather DMA engine (48w)"
	@echo "  make test-rapids                       RAPIDS descriptor-driven accelerator (48w)"
	@echo "  make test-bridge                       AXI4 crossbar bridge (sequential only — ~1GB per test) (serial)"
	@echo "  make test-converters                   Data width and protocol converters (48w)"
	@echo "  make test-apb-xbar                     APB crossbar (48w)"
	@echo "  make test-retro-legacy                 Retro legacy blocks (48w)"
	@echo "  make test-timing-char                  Timing characterization (48w)"
	@echo ""
	@echo "PER-LEVEL (append -gate, -func, or -full):"
	@echo "  make test-{name}-gate             GATE level"
	@echo "  make test-{name}-func             FUNC level"
	@echo "  make test-{name}-full             FULL level"
	@echo ""
	@echo "VARIANTS (append to any per-level target):"
	@echo "  ...-waves                         Enable waveform dump"
	@echo "  ...-serial                        Force sequential execution"
	@echo ""
	@echo "AGGREGATE:"
	@echo "  make test-all-gate                All envs, GATE, parallel"
	@echo "  make test-all-func                All envs, FUNC, parallel"
	@echo "  make test-all-full                All envs, FULL, parallel"
	@echo "  make test-all-{level}-serial      All envs, serial"
	@echo "  make test-all-{level}-waves       All envs, with waves"
	@echo ""
	@echo "COVERAGE:"
	@echo "  make coverage-val-common"
	@echo "  make coverage-val-amba"
	@echo "  make coverage-val-integ-common"
	@echo "  make coverage-val-integ-amba"
	@echo "  make coverage-stream"
	@echo "  make coverage-rapids"
	@echo "  make coverage-bridge"
	@echo "  make coverage-converters"
	@echo "  make coverage-apb-xbar"
	@echo "  make coverage-all                 All components"
	@echo "  make coverage-report-all          All reports"
	@echo "  make coverage-unified             Cross-component dashboard"
	@echo ""
	@echo "REGENERATE:"
	@echo "  python3 bin/generate_test_targets.py"
	@echo "================================================================================"

