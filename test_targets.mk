# ==============================================================================
# AUTO-GENERATED — do not edit manually
# Regenerate: python3 bin/generate_test_targets.py
# Source:     test_environments.toml
# ==============================================================================

PYTEST ?= python3 -m pytest

# --- val-common: RTL common modules (counters, arbiters, FIFOs, data integrity, etc.) ---

.PHONY: test-val-common
test-val-common:
	@echo "=== val-common FUNC (parallel) ==="
	@$(MAKE) -C val/common run-all-func-parallel

.PHONY: test-val-common-gate
test-val-common-gate:
	@echo "=== val-common GATE (parallel) ==="
	@$(MAKE) -C val/common run-all-gate-parallel

.PHONY: test-val-common-func
test-val-common-func:
	@echo "=== val-common FUNC (parallel) ==="
	@$(MAKE) -C val/common run-all-func-parallel

.PHONY: test-val-common-full
test-val-common-full:
	@echo "=== val-common FULL (parallel) ==="
	@$(MAKE) -C val/common run-all-full-parallel

.PHONY: test-val-common-gate-waves
test-val-common-gate-waves:
	@echo "=== val-common GATE (parallel + waves) ==="
	@$(MAKE) -C val/common run-all-gate-parallel-waves

.PHONY: test-val-common-func-waves
test-val-common-func-waves:
	@echo "=== val-common FUNC (parallel + waves) ==="
	@$(MAKE) -C val/common run-all-func-parallel-waves

.PHONY: test-val-common-full-waves
test-val-common-full-waves:
	@echo "=== val-common FULL (parallel + waves) ==="
	@$(MAKE) -C val/common run-all-full-parallel-waves

.PHONY: test-val-common-gate-serial
test-val-common-gate-serial:
	@echo "=== val-common GATE (serial) ==="
	@$(MAKE) -C val/common run-all-gate-serial

.PHONY: test-val-common-func-serial
test-val-common-func-serial:
	@echo "=== val-common FUNC (serial) ==="
	@$(MAKE) -C val/common run-all-func-serial

.PHONY: test-val-common-full-serial
test-val-common-full-serial:
	@echo "=== val-common FULL (serial) ==="
	@$(MAKE) -C val/common run-all-full-serial

.PHONY: coverage-val-common
coverage-val-common:
	@echo "=== val-common FUNC (parallel + coverage) ==="
	@COVERAGE=1 $(MAKE) -C val/common run-all-func-parallel

# --- val-cdc: Clock domain crossing primitives (rtl/cdc: gray/johnson counters, async FIFOs, handshakes) ---

.PHONY: test-val-cdc
test-val-cdc:
	@echo "=== val-cdc FUNC (parallel) ==="
	@$(MAKE) -C val/cdc run-all-func-parallel

.PHONY: test-val-cdc-gate
test-val-cdc-gate:
	@echo "=== val-cdc GATE (parallel) ==="
	@$(MAKE) -C val/cdc run-all-gate-parallel

.PHONY: test-val-cdc-func
test-val-cdc-func:
	@echo "=== val-cdc FUNC (parallel) ==="
	@$(MAKE) -C val/cdc run-all-func-parallel

.PHONY: test-val-cdc-full
test-val-cdc-full:
	@echo "=== val-cdc FULL (parallel) ==="
	@$(MAKE) -C val/cdc run-all-full-parallel

.PHONY: test-val-cdc-gate-waves
test-val-cdc-gate-waves:
	@echo "=== val-cdc GATE (parallel + waves) ==="
	@$(MAKE) -C val/cdc run-all-gate-parallel-waves

.PHONY: test-val-cdc-func-waves
test-val-cdc-func-waves:
	@echo "=== val-cdc FUNC (parallel + waves) ==="
	@$(MAKE) -C val/cdc run-all-func-parallel-waves

.PHONY: test-val-cdc-full-waves
test-val-cdc-full-waves:
	@echo "=== val-cdc FULL (parallel + waves) ==="
	@$(MAKE) -C val/cdc run-all-full-parallel-waves

.PHONY: test-val-cdc-gate-serial
test-val-cdc-gate-serial:
	@echo "=== val-cdc GATE (serial) ==="
	@$(MAKE) -C val/cdc run-all-gate-serial

.PHONY: test-val-cdc-func-serial
test-val-cdc-func-serial:
	@echo "=== val-cdc FUNC (serial) ==="
	@$(MAKE) -C val/cdc run-all-func-serial

.PHONY: test-val-cdc-full-serial
test-val-cdc-full-serial:
	@echo "=== val-cdc FULL (serial) ==="
	@$(MAKE) -C val/cdc run-all-full-serial

.PHONY: coverage-val-cdc
coverage-val-cdc:
	@echo "=== val-cdc FUNC (parallel + coverage) ==="
	@COVERAGE=1 $(MAKE) -C val/cdc run-all-func-parallel

# --- val-math: Arithmetic modules (rtl/math: adders, multipliers, dividers, encoders) ---

.PHONY: test-val-math
test-val-math:
	@echo "=== val-math FUNC (parallel) ==="
	@$(MAKE) -C val/math run-all-func-parallel

.PHONY: test-val-math-gate
test-val-math-gate:
	@echo "=== val-math GATE (parallel) ==="
	@$(MAKE) -C val/math run-all-gate-parallel

.PHONY: test-val-math-func
test-val-math-func:
	@echo "=== val-math FUNC (parallel) ==="
	@$(MAKE) -C val/math run-all-func-parallel

.PHONY: test-val-math-full
test-val-math-full:
	@echo "=== val-math FULL (parallel) ==="
	@$(MAKE) -C val/math run-all-full-parallel

.PHONY: test-val-math-gate-waves
test-val-math-gate-waves:
	@echo "=== val-math GATE (parallel + waves) ==="
	@$(MAKE) -C val/math run-all-gate-parallel-waves

.PHONY: test-val-math-func-waves
test-val-math-func-waves:
	@echo "=== val-math FUNC (parallel + waves) ==="
	@$(MAKE) -C val/math run-all-func-parallel-waves

.PHONY: test-val-math-full-waves
test-val-math-full-waves:
	@echo "=== val-math FULL (parallel + waves) ==="
	@$(MAKE) -C val/math run-all-full-parallel-waves

.PHONY: test-val-math-gate-serial
test-val-math-gate-serial:
	@echo "=== val-math GATE (serial) ==="
	@$(MAKE) -C val/math run-all-gate-serial

.PHONY: test-val-math-func-serial
test-val-math-func-serial:
	@echo "=== val-math FUNC (serial) ==="
	@$(MAKE) -C val/math run-all-func-serial

.PHONY: test-val-math-full-serial
test-val-math-full-serial:
	@echo "=== val-math FULL (serial) ==="
	@$(MAKE) -C val/math run-all-full-serial

.PHONY: coverage-val-math
coverage-val-math:
	@echo "=== val-math FUNC (parallel + coverage) ==="
	@COVERAGE=1 $(MAKE) -C val/math run-all-func-parallel

# --- val-amba: AMBA protocol modules (AXI4, APB, AXIS monitors) ---

.PHONY: test-val-amba
test-val-amba:
	@echo "=== val-amba FUNC (parallel) ==="
	@$(MAKE) -C val/amba run-all-func-parallel

.PHONY: test-val-amba-gate
test-val-amba-gate:
	@echo "=== val-amba GATE (parallel) ==="
	@$(MAKE) -C val/amba run-all-gate-parallel

.PHONY: test-val-amba-func
test-val-amba-func:
	@echo "=== val-amba FUNC (parallel) ==="
	@$(MAKE) -C val/amba run-all-func-parallel

.PHONY: test-val-amba-full
test-val-amba-full:
	@echo "=== val-amba FULL (parallel) ==="
	@$(MAKE) -C val/amba run-all-full-parallel

.PHONY: test-val-amba-gate-waves
test-val-amba-gate-waves:
	@echo "=== val-amba GATE (parallel + waves) ==="
	@$(MAKE) -C val/amba run-all-gate-parallel-waves

.PHONY: test-val-amba-func-waves
test-val-amba-func-waves:
	@echo "=== val-amba FUNC (parallel + waves) ==="
	@$(MAKE) -C val/amba run-all-func-parallel-waves

.PHONY: test-val-amba-full-waves
test-val-amba-full-waves:
	@echo "=== val-amba FULL (parallel + waves) ==="
	@$(MAKE) -C val/amba run-all-full-parallel-waves

.PHONY: test-val-amba-gate-serial
test-val-amba-gate-serial:
	@echo "=== val-amba GATE (serial) ==="
	@$(MAKE) -C val/amba run-all-gate-serial

.PHONY: test-val-amba-func-serial
test-val-amba-func-serial:
	@echo "=== val-amba FUNC (serial) ==="
	@$(MAKE) -C val/amba run-all-func-serial

.PHONY: test-val-amba-full-serial
test-val-amba-full-serial:
	@echo "=== val-amba FULL (serial) ==="
	@$(MAKE) -C val/amba run-all-full-serial

.PHONY: coverage-val-amba
coverage-val-amba:
	@echo "=== val-amba FUNC (parallel + coverage) ==="
	@COVERAGE=1 $(MAKE) -C val/amba run-all-func-parallel

# --- val-amba-monitor-lite: AXI monitor-lite (axi_monitor_lite through the monitored wrappers) ---

.PHONY: test-val-amba-monitor-lite
test-val-amba-monitor-lite:
	@echo "=== val-amba-monitor-lite FUNC (parallel) ==="
	@$(MAKE) -C val/amba/monitor-lite run-all-func-parallel

.PHONY: test-val-amba-monitor-lite-gate
test-val-amba-monitor-lite-gate:
	@echo "=== val-amba-monitor-lite GATE (parallel) ==="
	@$(MAKE) -C val/amba/monitor-lite run-all-gate-parallel

.PHONY: test-val-amba-monitor-lite-func
test-val-amba-monitor-lite-func:
	@echo "=== val-amba-monitor-lite FUNC (parallel) ==="
	@$(MAKE) -C val/amba/monitor-lite run-all-func-parallel

.PHONY: test-val-amba-monitor-lite-full
test-val-amba-monitor-lite-full:
	@echo "=== val-amba-monitor-lite FULL (parallel) ==="
	@$(MAKE) -C val/amba/monitor-lite run-all-full-parallel

.PHONY: test-val-amba-monitor-lite-gate-waves
test-val-amba-monitor-lite-gate-waves:
	@echo "=== val-amba-monitor-lite GATE (parallel + waves) ==="
	@$(MAKE) -C val/amba/monitor-lite run-all-gate-parallel-waves

.PHONY: test-val-amba-monitor-lite-func-waves
test-val-amba-monitor-lite-func-waves:
	@echo "=== val-amba-monitor-lite FUNC (parallel + waves) ==="
	@$(MAKE) -C val/amba/monitor-lite run-all-func-parallel-waves

.PHONY: test-val-amba-monitor-lite-full-waves
test-val-amba-monitor-lite-full-waves:
	@echo "=== val-amba-monitor-lite FULL (parallel + waves) ==="
	@$(MAKE) -C val/amba/monitor-lite run-all-full-parallel-waves

.PHONY: test-val-amba-monitor-lite-gate-serial
test-val-amba-monitor-lite-gate-serial:
	@echo "=== val-amba-monitor-lite GATE (serial) ==="
	@$(MAKE) -C val/amba/monitor-lite run-all-gate-serial

.PHONY: test-val-amba-monitor-lite-func-serial
test-val-amba-monitor-lite-func-serial:
	@echo "=== val-amba-monitor-lite FUNC (serial) ==="
	@$(MAKE) -C val/amba/monitor-lite run-all-func-serial

.PHONY: test-val-amba-monitor-lite-full-serial
test-val-amba-monitor-lite-full-serial:
	@echo "=== val-amba-monitor-lite FULL (serial) ==="
	@$(MAKE) -C val/amba/monitor-lite run-all-full-serial

.PHONY: coverage-val-amba-monitor-lite
coverage-val-amba-monitor-lite:
	@echo "=== val-amba-monitor-lite FUNC (parallel + coverage) ==="
	@COVERAGE=1 $(MAKE) -C val/amba/monitor-lite run-all-func-parallel

# --- stream: STREAM scatter-gather DMA engine ---

.PHONY: test-stream
test-stream:
	@echo "=== stream FUNC (parallel) ==="
	@$(MAKE) -C projects/components/dmas/stream/dv/tests run-all-func-parallel

.PHONY: test-stream-gate
test-stream-gate:
	@echo "=== stream GATE (parallel) ==="
	@$(MAKE) -C projects/components/dmas/stream/dv/tests run-all-gate-parallel

.PHONY: test-stream-func
test-stream-func:
	@echo "=== stream FUNC (parallel) ==="
	@$(MAKE) -C projects/components/dmas/stream/dv/tests run-all-func-parallel

.PHONY: test-stream-full
test-stream-full:
	@echo "=== stream FULL (parallel) ==="
	@$(MAKE) -C projects/components/dmas/stream/dv/tests run-all-full-parallel

.PHONY: test-stream-gate-waves
test-stream-gate-waves:
	@echo "=== stream GATE (parallel + waves) ==="
	@$(MAKE) -C projects/components/dmas/stream/dv/tests run-all-gate-parallel-waves

.PHONY: test-stream-func-waves
test-stream-func-waves:
	@echo "=== stream FUNC (parallel + waves) ==="
	@$(MAKE) -C projects/components/dmas/stream/dv/tests run-all-func-parallel-waves

.PHONY: test-stream-full-waves
test-stream-full-waves:
	@echo "=== stream FULL (parallel + waves) ==="
	@$(MAKE) -C projects/components/dmas/stream/dv/tests run-all-full-parallel-waves

.PHONY: test-stream-gate-serial
test-stream-gate-serial:
	@echo "=== stream GATE (serial) ==="
	@$(MAKE) -C projects/components/dmas/stream/dv/tests run-all-gate-serial

.PHONY: test-stream-func-serial
test-stream-func-serial:
	@echo "=== stream FUNC (serial) ==="
	@$(MAKE) -C projects/components/dmas/stream/dv/tests run-all-func-serial

.PHONY: test-stream-full-serial
test-stream-full-serial:
	@echo "=== stream FULL (serial) ==="
	@$(MAKE) -C projects/components/dmas/stream/dv/tests run-all-full-serial

.PHONY: coverage-stream
coverage-stream:
	@echo "=== stream coverage ==="
	@$(MAKE) -C projects/components/dmas/stream/dv/tests fresh-coverage

.PHONY: coverage-report-stream
coverage-report-stream:
	@echo "=== stream coverage report ==="
	@$(MAKE) -C projects/components/dmas/stream/dv/tests coverage-report

# --- rapids: RAPIDS descriptor-driven accelerator ---

.PHONY: test-rapids
test-rapids:
	@echo "=== rapids FUNC (parallel) ==="
	@$(MAKE) -C projects/components/dmas/rapids/dv/tests run-all-func-parallel

.PHONY: test-rapids-gate
test-rapids-gate:
	@echo "=== rapids GATE (parallel) ==="
	@$(MAKE) -C projects/components/dmas/rapids/dv/tests run-all-gate-parallel

.PHONY: test-rapids-func
test-rapids-func:
	@echo "=== rapids FUNC (parallel) ==="
	@$(MAKE) -C projects/components/dmas/rapids/dv/tests run-all-func-parallel

.PHONY: test-rapids-full
test-rapids-full:
	@echo "=== rapids FULL (parallel) ==="
	@$(MAKE) -C projects/components/dmas/rapids/dv/tests run-all-full-parallel

.PHONY: test-rapids-gate-waves
test-rapids-gate-waves:
	@echo "=== rapids GATE (parallel + waves) ==="
	@$(MAKE) -C projects/components/dmas/rapids/dv/tests run-all-gate-parallel-waves

.PHONY: test-rapids-func-waves
test-rapids-func-waves:
	@echo "=== rapids FUNC (parallel + waves) ==="
	@$(MAKE) -C projects/components/dmas/rapids/dv/tests run-all-func-parallel-waves

.PHONY: test-rapids-full-waves
test-rapids-full-waves:
	@echo "=== rapids FULL (parallel + waves) ==="
	@$(MAKE) -C projects/components/dmas/rapids/dv/tests run-all-full-parallel-waves

.PHONY: test-rapids-gate-serial
test-rapids-gate-serial:
	@echo "=== rapids GATE (serial) ==="
	@$(MAKE) -C projects/components/dmas/rapids/dv/tests run-all-gate-serial

.PHONY: test-rapids-func-serial
test-rapids-func-serial:
	@echo "=== rapids FUNC (serial) ==="
	@$(MAKE) -C projects/components/dmas/rapids/dv/tests run-all-func-serial

.PHONY: test-rapids-full-serial
test-rapids-full-serial:
	@echo "=== rapids FULL (serial) ==="
	@$(MAKE) -C projects/components/dmas/rapids/dv/tests run-all-full-serial

.PHONY: coverage-rapids
coverage-rapids:
	@echo "=== rapids coverage ==="
	@$(MAKE) -C projects/components/dmas/rapids/dv/tests coverage-full-report

.PHONY: coverage-report-rapids
coverage-report-rapids:
	@echo "=== rapids coverage report ==="
	@$(MAKE) -C projects/components/dmas/rapids/dv/tests coverage-report

# --- bridge: AXI4 crossbar bridge (sequential only — ~1GB per test) ---

.PHONY: test-bridge
test-bridge:
	@echo "=== bridge FUNC (serial) ==="
	@$(MAKE) -C projects/components/bridge/dv/tests run-all-func-serial

.PHONY: test-bridge-gate
test-bridge-gate:
	@echo "=== bridge GATE (serial) ==="
	@$(MAKE) -C projects/components/bridge/dv/tests run-all-gate-serial

.PHONY: test-bridge-func
test-bridge-func:
	@echo "=== bridge FUNC (serial) ==="
	@$(MAKE) -C projects/components/bridge/dv/tests run-all-func-serial

.PHONY: test-bridge-full
test-bridge-full:
	@echo "=== bridge FULL (serial) ==="
	@$(MAKE) -C projects/components/bridge/dv/tests run-all-full-serial

.PHONY: test-bridge-gate-waves
test-bridge-gate-waves:
	@echo "=== bridge GATE (serial + waves) ==="
	@$(MAKE) -C projects/components/bridge/dv/tests run-all-gate-serial-waves

.PHONY: test-bridge-func-waves
test-bridge-func-waves:
	@echo "=== bridge FUNC (serial + waves) ==="
	@$(MAKE) -C projects/components/bridge/dv/tests run-all-func-serial-waves

.PHONY: test-bridge-full-waves
test-bridge-full-waves:
	@echo "=== bridge FULL (serial + waves) ==="
	@$(MAKE) -C projects/components/bridge/dv/tests run-all-full-serial-waves

.PHONY: test-bridge-gate-serial
test-bridge-gate-serial:
	@echo "=== bridge GATE (serial) ==="
	@$(MAKE) -C projects/components/bridge/dv/tests run-all-gate-serial

.PHONY: test-bridge-func-serial
test-bridge-func-serial:
	@echo "=== bridge FUNC (serial) ==="
	@$(MAKE) -C projects/components/bridge/dv/tests run-all-func-serial

.PHONY: test-bridge-full-serial
test-bridge-full-serial:
	@echo "=== bridge FULL (serial) ==="
	@$(MAKE) -C projects/components/bridge/dv/tests run-all-full-serial

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
	@$(MAKE) -C projects/components/converters/dv/tests run-all-func-parallel

.PHONY: test-converters-gate
test-converters-gate:
	@echo "=== converters GATE (parallel) ==="
	@$(MAKE) -C projects/components/converters/dv/tests run-all-gate-parallel

.PHONY: test-converters-func
test-converters-func:
	@echo "=== converters FUNC (parallel) ==="
	@$(MAKE) -C projects/components/converters/dv/tests run-all-func-parallel

.PHONY: test-converters-full
test-converters-full:
	@echo "=== converters FULL (parallel) ==="
	@$(MAKE) -C projects/components/converters/dv/tests run-all-full-parallel

.PHONY: test-converters-gate-waves
test-converters-gate-waves:
	@echo "=== converters GATE (parallel + waves) ==="
	@$(MAKE) -C projects/components/converters/dv/tests run-all-gate-parallel-waves

.PHONY: test-converters-func-waves
test-converters-func-waves:
	@echo "=== converters FUNC (parallel + waves) ==="
	@$(MAKE) -C projects/components/converters/dv/tests run-all-func-parallel-waves

.PHONY: test-converters-full-waves
test-converters-full-waves:
	@echo "=== converters FULL (parallel + waves) ==="
	@$(MAKE) -C projects/components/converters/dv/tests run-all-full-parallel-waves

.PHONY: test-converters-gate-serial
test-converters-gate-serial:
	@echo "=== converters GATE (serial) ==="
	@$(MAKE) -C projects/components/converters/dv/tests run-all-gate-serial

.PHONY: test-converters-func-serial
test-converters-func-serial:
	@echo "=== converters FUNC (serial) ==="
	@$(MAKE) -C projects/components/converters/dv/tests run-all-func-serial

.PHONY: test-converters-full-serial
test-converters-full-serial:
	@echo "=== converters FULL (serial) ==="
	@$(MAKE) -C projects/components/converters/dv/tests run-all-full-serial

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
	@$(MAKE) -C projects/components/apbx-xbar/dv/tests run-all-func-parallel

.PHONY: test-apb-xbar-gate
test-apb-xbar-gate:
	@echo "=== apb-xbar GATE (parallel) ==="
	@$(MAKE) -C projects/components/apbx-xbar/dv/tests run-all-gate-parallel

.PHONY: test-apb-xbar-func
test-apb-xbar-func:
	@echo "=== apb-xbar FUNC (parallel) ==="
	@$(MAKE) -C projects/components/apbx-xbar/dv/tests run-all-func-parallel

.PHONY: test-apb-xbar-full
test-apb-xbar-full:
	@echo "=== apb-xbar FULL (parallel) ==="
	@$(MAKE) -C projects/components/apbx-xbar/dv/tests run-all-full-parallel

.PHONY: test-apb-xbar-gate-waves
test-apb-xbar-gate-waves:
	@echo "=== apb-xbar GATE (parallel + waves) ==="
	@$(MAKE) -C projects/components/apbx-xbar/dv/tests run-all-gate-parallel-waves

.PHONY: test-apb-xbar-func-waves
test-apb-xbar-func-waves:
	@echo "=== apb-xbar FUNC (parallel + waves) ==="
	@$(MAKE) -C projects/components/apbx-xbar/dv/tests run-all-func-parallel-waves

.PHONY: test-apb-xbar-full-waves
test-apb-xbar-full-waves:
	@echo "=== apb-xbar FULL (parallel + waves) ==="
	@$(MAKE) -C projects/components/apbx-xbar/dv/tests run-all-full-parallel-waves

.PHONY: test-apb-xbar-gate-serial
test-apb-xbar-gate-serial:
	@echo "=== apb-xbar GATE (serial) ==="
	@$(MAKE) -C projects/components/apbx-xbar/dv/tests run-all-gate-serial

.PHONY: test-apb-xbar-func-serial
test-apb-xbar-func-serial:
	@echo "=== apb-xbar FUNC (serial) ==="
	@$(MAKE) -C projects/components/apbx-xbar/dv/tests run-all-func-serial

.PHONY: test-apb-xbar-full-serial
test-apb-xbar-full-serial:
	@echo "=== apb-xbar FULL (serial) ==="
	@$(MAKE) -C projects/components/apbx-xbar/dv/tests run-all-full-serial

.PHONY: coverage-apb-xbar
coverage-apb-xbar:
	@echo "=== apb-xbar FUNC (parallel + coverage) ==="
	@COVERAGE=1 $(MAKE) -C projects/components/apbx-xbar/dv/tests run-all-func-parallel

# --- retro-legacy: Retro legacy blocks ---

.PHONY: test-retro-legacy
test-retro-legacy:
	@echo "=== retro-legacy FUNC (parallel) ==="
	@$(MAKE) -C projects/components/retro_legacy_blocks/dv/tests run-all-func-parallel

.PHONY: test-retro-legacy-gate
test-retro-legacy-gate:
	@echo "=== retro-legacy GATE (parallel) ==="
	@$(MAKE) -C projects/components/retro_legacy_blocks/dv/tests run-all-gate-parallel

.PHONY: test-retro-legacy-func
test-retro-legacy-func:
	@echo "=== retro-legacy FUNC (parallel) ==="
	@$(MAKE) -C projects/components/retro_legacy_blocks/dv/tests run-all-func-parallel

.PHONY: test-retro-legacy-full
test-retro-legacy-full:
	@echo "=== retro-legacy FULL (parallel) ==="
	@$(MAKE) -C projects/components/retro_legacy_blocks/dv/tests run-all-full-parallel

.PHONY: test-retro-legacy-gate-waves
test-retro-legacy-gate-waves:
	@echo "=== retro-legacy GATE (parallel + waves) ==="
	@$(MAKE) -C projects/components/retro_legacy_blocks/dv/tests run-all-gate-parallel-waves

.PHONY: test-retro-legacy-func-waves
test-retro-legacy-func-waves:
	@echo "=== retro-legacy FUNC (parallel + waves) ==="
	@$(MAKE) -C projects/components/retro_legacy_blocks/dv/tests run-all-func-parallel-waves

.PHONY: test-retro-legacy-full-waves
test-retro-legacy-full-waves:
	@echo "=== retro-legacy FULL (parallel + waves) ==="
	@$(MAKE) -C projects/components/retro_legacy_blocks/dv/tests run-all-full-parallel-waves

.PHONY: test-retro-legacy-gate-serial
test-retro-legacy-gate-serial:
	@echo "=== retro-legacy GATE (serial) ==="
	@$(MAKE) -C projects/components/retro_legacy_blocks/dv/tests run-all-gate-serial

.PHONY: test-retro-legacy-func-serial
test-retro-legacy-func-serial:
	@echo "=== retro-legacy FUNC (serial) ==="
	@$(MAKE) -C projects/components/retro_legacy_blocks/dv/tests run-all-func-serial

.PHONY: test-retro-legacy-full-serial
test-retro-legacy-full-serial:
	@echo "=== retro-legacy FULL (serial) ==="
	@$(MAKE) -C projects/components/retro_legacy_blocks/dv/tests run-all-full-serial

# --- timing-char: Timing characterization ---

.PHONY: test-timing-char
test-timing-char:
	@echo "=== timing-char FUNC (parallel) ==="
	@$(MAKE) -C projects/asic-trials/timing_characterization/dv/tests run-all-func-parallel

.PHONY: test-timing-char-gate
test-timing-char-gate:
	@echo "=== timing-char GATE (parallel) ==="
	@$(MAKE) -C projects/asic-trials/timing_characterization/dv/tests run-all-gate-parallel

.PHONY: test-timing-char-func
test-timing-char-func:
	@echo "=== timing-char FUNC (parallel) ==="
	@$(MAKE) -C projects/asic-trials/timing_characterization/dv/tests run-all-func-parallel

.PHONY: test-timing-char-full
test-timing-char-full:
	@echo "=== timing-char FULL (parallel) ==="
	@$(MAKE) -C projects/asic-trials/timing_characterization/dv/tests run-all-full-parallel

.PHONY: test-timing-char-gate-waves
test-timing-char-gate-waves:
	@echo "=== timing-char GATE (parallel + waves) ==="
	@$(MAKE) -C projects/asic-trials/timing_characterization/dv/tests run-all-gate-parallel-waves

.PHONY: test-timing-char-func-waves
test-timing-char-func-waves:
	@echo "=== timing-char FUNC (parallel + waves) ==="
	@$(MAKE) -C projects/asic-trials/timing_characterization/dv/tests run-all-func-parallel-waves

.PHONY: test-timing-char-full-waves
test-timing-char-full-waves:
	@echo "=== timing-char FULL (parallel + waves) ==="
	@$(MAKE) -C projects/asic-trials/timing_characterization/dv/tests run-all-full-parallel-waves

.PHONY: test-timing-char-gate-serial
test-timing-char-gate-serial:
	@echo "=== timing-char GATE (serial) ==="
	@$(MAKE) -C projects/asic-trials/timing_characterization/dv/tests run-all-gate-serial

.PHONY: test-timing-char-func-serial
test-timing-char-func-serial:
	@echo "=== timing-char FUNC (serial) ==="
	@$(MAKE) -C projects/asic-trials/timing_characterization/dv/tests run-all-func-serial

.PHONY: test-timing-char-full-serial
test-timing-char-full-serial:
	@echo "=== timing-char FULL (serial) ==="
	@$(MAKE) -C projects/asic-trials/timing_characterization/dv/tests run-all-full-serial

# ==============================================================================
# Aggregate targets — all environments
# ==============================================================================

.PHONY: test-all-gate
test-all-gate: test-val-common-gate test-val-cdc-gate test-val-math-gate test-val-amba-gate test-val-amba-monitor-lite-gate test-stream-gate test-rapids-gate test-bridge-gate test-converters-gate test-apb-xbar-gate test-retro-legacy-gate test-timing-char-gate

.PHONY: test-all-func
test-all-func: test-val-common-func test-val-cdc-func test-val-math-func test-val-amba-func test-val-amba-monitor-lite-func test-stream-func test-rapids-func test-bridge-func test-converters-func test-apb-xbar-func test-retro-legacy-func test-timing-char-func

.PHONY: test-all-full
test-all-full: test-val-common-full test-val-cdc-full test-val-math-full test-val-amba-full test-val-amba-monitor-lite-full test-stream-full test-rapids-full test-bridge-full test-converters-full test-apb-xbar-full test-retro-legacy-full test-timing-char-full

.PHONY: test-all-gate-serial
test-all-gate-serial: test-val-common-gate-serial test-val-cdc-gate-serial test-val-math-gate-serial test-val-amba-gate-serial test-val-amba-monitor-lite-gate-serial test-stream-gate-serial test-rapids-gate-serial test-bridge-gate-serial test-converters-gate-serial test-apb-xbar-gate-serial test-retro-legacy-gate-serial test-timing-char-gate-serial

.PHONY: test-all-func-serial
test-all-func-serial: test-val-common-func-serial test-val-cdc-func-serial test-val-math-func-serial test-val-amba-func-serial test-val-amba-monitor-lite-func-serial test-stream-func-serial test-rapids-func-serial test-bridge-func-serial test-converters-func-serial test-apb-xbar-func-serial test-retro-legacy-func-serial test-timing-char-func-serial

.PHONY: test-all-full-serial
test-all-full-serial: test-val-common-full-serial test-val-cdc-full-serial test-val-math-full-serial test-val-amba-full-serial test-val-amba-monitor-lite-full-serial test-stream-full-serial test-rapids-full-serial test-bridge-full-serial test-converters-full-serial test-apb-xbar-full-serial test-retro-legacy-full-serial test-timing-char-full-serial

.PHONY: test-all-gate-waves
test-all-gate-waves: test-val-common-gate-waves test-val-cdc-gate-waves test-val-math-gate-waves test-val-amba-gate-waves test-val-amba-monitor-lite-gate-waves test-stream-gate-waves test-rapids-gate-waves test-bridge-gate-waves test-converters-gate-waves test-apb-xbar-gate-waves test-retro-legacy-gate-waves test-timing-char-gate-waves

.PHONY: test-all-func-waves
test-all-func-waves: test-val-common-func-waves test-val-cdc-func-waves test-val-math-func-waves test-val-amba-func-waves test-val-amba-monitor-lite-func-waves test-stream-func-waves test-rapids-func-waves test-bridge-func-waves test-converters-func-waves test-apb-xbar-func-waves test-retro-legacy-func-waves test-timing-char-func-waves

.PHONY: test-all-full-waves
test-all-full-waves: test-val-common-full-waves test-val-cdc-full-waves test-val-math-full-waves test-val-amba-full-waves test-val-amba-monitor-lite-full-waves test-stream-full-waves test-rapids-full-waves test-bridge-full-waves test-converters-full-waves test-apb-xbar-full-waves test-retro-legacy-full-waves test-timing-char-full-waves

.PHONY: coverage-all
coverage-all: coverage-val-common coverage-val-cdc coverage-val-math coverage-val-amba coverage-val-amba-monitor-lite coverage-stream coverage-rapids coverage-bridge coverage-converters coverage-apb-xbar

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
	@echo "  make test-val-common                   RTL common modules (counters, arbiters, FIFOs, data integrity, etc.) (parallel)"
	@echo "  make test-val-cdc                      Clock domain crossing primitives (rtl/cdc: gray/johnson counters, async FIFOs, handshakes) (parallel)"
	@echo "  make test-val-math                     Arithmetic modules (rtl/math: adders, multipliers, dividers, encoders) (parallel)"
	@echo "  make test-val-amba                     AMBA protocol modules (AXI4, APB, AXIS monitors) (parallel)"
	@echo "  make test-val-amba-monitor-lite        AXI monitor-lite (axi_monitor_lite through the monitored wrappers) (parallel)"
	@echo "  make test-stream                       STREAM scatter-gather DMA engine (parallel)"
	@echo "  make test-rapids                       RAPIDS descriptor-driven accelerator (parallel)"
	@echo "  make test-bridge                       AXI4 crossbar bridge (sequential only — ~1GB per test) (serial)"
	@echo "  make test-converters                   Data width and protocol converters (parallel)"
	@echo "  make test-apb-xbar                     APB crossbar (parallel)"
	@echo "  make test-retro-legacy                 Retro legacy blocks (parallel)"
	@echo "  make test-timing-char                  Timing characterization (parallel)"
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
	@echo "  make coverage-val-cdc"
	@echo "  make coverage-val-math"
	@echo "  make coverage-val-amba"
	@echo "  make coverage-val-amba-monitor-lite"
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

