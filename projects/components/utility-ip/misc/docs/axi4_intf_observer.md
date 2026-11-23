# AXI4 Interface Observers

**Modules:** `axi4_intf_master_observer`, `axi4_intf_slave_observer`, `axi4_intf_master_observer_full`, `axi4_intf_slave_observer_full`
**Location:** `projects/components/utility-ip/misc/rtl/`
**Status:** Verified in simulation; full variants characterized by out-of-context FPGA synthesis

## Overview

The AXI4 interface observers sit beside an AXI link and watch its actual
handshakes. Every observed signal, including ready, is an input. They do not
insert an endpoint or drive the observed bus.

Two monitor families share one implementation and one `obs_regs` register map:

| Public modules | Tap family | Intended use |
|---|---|---|
| `axi4_intf_master_observer`, `axi4_intf_slave_observer` | `axi4_*_monlite` | Existing FPGA/project integrations and lightweight event coverage |
| `axi4_intf_master_observer_full`, `axi4_intf_slave_observer_full` | Passive full Ocelus taps | Performance windows, debug state changes, threshold/timeout/error/completion coverage, and full transaction tracking |

The shared core owns the APB register block, bus meters, latency histograms,
MonBus arbiter, and AXIL/AXI egress groups. The existing public lite names and
defaults are unchanged. Full variants are new tops; no existing project was
switched to them.

## Passive full taps

`axi4_rd_monfull_snoop` and `axi4_wr_monfull_snoop` adapt actual command,
data, and response handshakes to `axi_monitor_filtered`. They contain no AXI
skid endpoint and no ready output. The full monitor's `block_ready` is left
unconnected to observation.

The read tap observes AR and R. The write tap observes AW, W, and B and
preserves `USE_WDATA_ORDER_Q` and `NUM_BANKS`, including same-cycle AW+W.
Master full taps support the existing per-port ID slice using
`CH_BASE + port * NUM_CHANNELS`; an excluded ID creates neither a transaction
entry nor a refusal.

## Configuration and capabilities

The full variants connect the existing register fields for:

- error, timeout, completion, threshold, performance, and debug enables
- packet/event masks
- address-range checks and per-range flavors
- performance-window start/end selection and manual triggers
- timeout and latency thresholds

`OBS_CAPS0` reports the cones actually built. Full performance/debug capability
bits follow `TAP_ENABLE_PERF_LOGIC` and `TAP_ENABLE_DEBUG_LOGIC`; the lite bits
remain zero because those cones do not exist in `axi_monitor_lite`.
`OBS_CAPS1/2` retain their port, channel, bank, and transaction-capacity
meanings.

## Observation-loss accounting

`cmd_refused` is an actual accepted command that has neither a same-ID pending
merge nor a transaction-table allocation. It covers both physical table
fullness and the command-entry reserve cap. It does not assert for:

- valid without ready
- a same-ID pending merge
- an ID excluded by the observer's slice
- a successful allocation after capacity becomes available

Each passive tap saturates a 16-bit refused counter, cleared by reset or its
monitor clear epoch. Reporter backpressure is not counted as a dropped packet;
the full tap's `dropped_count` is zero. Sustained backpressure can eventually
fill the transaction table and appear as refused coverage. A nonzero refused
count raises `OBS_STICKY.TAP_BLOCKED`, telling software that observation was
incomplete even though the observed bus continued.

## Verification

The observer suite covers register capabilities, default traffic, all full
packet classes, explicit performance-window open/close, debug events, fixed-
cycle external acceptance under MonBus backpressure, table saturation, exact
refusal accounting, ID-slice exclusion, banked same-cycle AW+W, clear/reuse,
normal reset/reissue, and zero-clock reset recovery.

Run it with:

```bash
source env_python
make -C projects/components/utility-ip/misc/dv/tests/fub clean-all
make -C projects/components/utility-ip/misc/dv/tests/fub run-axi4_intf_observer-full-parallel
```

The full-monitor transaction-manager, base, filtered, reporter, and AXI4
wrapper formal harnesses cover the new status path. A golden CAM equivalence
harness lives in `formal/amba/monitor_trans_cam/`.

## FPGA characterization

Measure full and context-lite rows with:

```bash
source env_python
RUN_LABEL=<label> JOBS=4 rtl/amba/fpga/bin/full_observer_synth_sweep.sh
```

The unoptimized full baseline missed the selected register-to-register timing
targets. Three conversions—CAM payload reset removal, reporter snapshot reset
removal, and lowest-set CAM allocation—were functionally verified but increased
LUT count without a consistent timing benefit, so all three were reverted.
Their absolute values and deltas are in
`docs/markdown/rtl-amba/monitor/monitor_characterization.md`.

Use the full variants when their unique features are required and their cost
and timing are acceptable for the integration. They are not presented as a
replacement for the lighter existing observers. Residual timing misses must be
addressed by a separately measured integration-specific design, not hidden by
disabling features after the comparison.

## References

- `docs/superpowers/specs/2026-11-22-full-monitor-fpga-observers-design.md` — architecture and comparison contract.
- `docs/markdown/rtl-amba/monitor/monitor_characterization.md` — baseline, experiments, and residual timing.
- `vault/handbook/design/observers-do-not-drive.md` — passive observation and loss-reporting rule.
