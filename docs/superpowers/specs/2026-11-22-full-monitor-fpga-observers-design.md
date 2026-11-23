# FPGA-Optimized Full-Monitor Observers Design

**Date:** 2026-11-22
**Status:** Approved design; implementation not yet planned
**Scope:** AXI4 interface observers, passive full-monitor taps, full Ocelus monitor FPGA optimization, and measurement collateral

## 1. Purpose

Add reusable full-feature versions of the AXI4 master and slave interface observers and measure whether FPGA-oriented changes make the existing full Ocelus monitor substantially more efficient. The current lite observers and every existing project integration remain unchanged.

The primary comparison is **the same full observer before and after optimization**. Lite observers are secondary size context, not feature-equivalent controls. An area reduction obtained by removing a full-monitor feature, changing packet semantics, or weakening observation-loss reporting is not an optimization win.

The work has two independently useful deliverables:

1. Correct, passive, full-feature observer variants.
2. A reproducible account of which full-monitor FPGA optimizations helped, which did not, and by how much.

The full observer variants remain deliverables even if the measured optimization gain is small or negative.

## 2. Current State and Rationale

`axi4_intf_master_observer` and `axi4_intf_slave_observer` currently instantiate `axi4_*_monlite` taps. Their bodies also contain the APB/PeakRDL configuration block, AXI bus meters, latency histograms, MonBus arbitration, and MonBus egress groups. Copying those bodies to make full variants would duplicate roughly 3,200 lines and create two families that could drift.

The existing full `axi4_*_mon` wrappers are in-path endpoint wrappers. Their `block_ready` output can gate the wrapped endpoint. Leaving their ready outputs unconnected prevents them from driving the external observed bus, but does not make them correct passive taps: internal gating can still make the monitor miss a command that the real bus accepted.

The new full variants therefore use `axi_monitor_filtered` through passive tap adapters. The adapters observe the actual external handshakes and never feed monitor readiness back into those handshakes.

## 3. Requirements

### 3.1 Functional requirements

- Preserve the existing public modules `axi4_intf_master_observer` and `axi4_intf_slave_observer`, including their ports, parameter defaults, lite monitoring behavior, and register map.
- Add public modules `axi4_intf_master_observer_full` and `axi4_intf_slave_observer_full` with the corresponding observer interfaces and the existing observer parameter defaults.
- Expose all existing full-monitor cone controls, including performance-window and debug controls already present in `obs_regs`.
- Report `OBS_CAPS0` according to the cones actually built in each variant. In particular, full variants may advertise performance/debug cones only when those cones exist; lite behavior remains unchanged.
- Observe actual command, data, and response handshakes. No full-monitor signal may gate, repeat, delay, or otherwise alter the observed bus.
- Count commands accepted by the observed bus but refused by the full transaction table because its command-entry capacity is exhausted.
- Preserve reporter backpressure as backpressure. Do not label a held reporter event as dropped. Sustained output backpressure may eventually cause table refusal, which must be visible through the refused counters and `OBS_STICKY.TAP_BLOCKED`.
- Preserve full-monitor packet contents, event ordering, timeout behavior, performance windows, debug events, address checks, and runtime-enable semantics across optimization.

### 3.2 Integration requirements

- Use one shared implementation for each observer role, parameterized only at the monitor-tap selection and capability reporting points.
- Keep the current observer names as thin lite wrappers. Add separate thin full wrappers rather than requiring existing consumers to select a new parameter.
- Add two role-independent passive tap modules:
  - `axi4_rd_monfull_snoop`
  - `axi4_wr_monfull_snoop`
- Do not switch any existing project, bridge configuration, STREAM/RAPIDS integration, or board build to a full variant.
- Register every new module filelist in `bin/filelists.toml`; do not edit generated register RTL by hand.
- Keep unrelated active work, including Onyx/cache-reference changes and generated/report churn, out of every commit.

### 3.3 Non-goals

- Replacing lite monitors in existing projects.
- Making full and lite monitors feature-equivalent.
- Adding a new register map or regenerating `obs_regs`; the approved design uses the existing map.
- Optimizing APB, CHI, ACE, AXIS, CXS, or cache-specific monitors in this work item.
- Claiming board-level timing closure from OOC results alone.
- Chasing an area number by reducing `MAX_TRANSACTIONS`, disabling cones, or changing the comparison configuration between baseline and optimized builds.

## 4. Architecture

### 4.1 Shared observer cores and public wrappers

Move the existing observer bodies to internal core modules, one for the master role and one for the slave role. A `MONITOR_FAMILY` parameter selects lite or full taps. Everything outside tap selection and truthful capability reporting remains common:

- APB configuration and generated `obs_regs` interface
- configuration aliases and range decoding
- AXI bus meters
- latency histograms
- MonBus arbiter and timestamp
- AXIL/AXI egress groups
- telemetry readback

Four thin public wrappers provide the stable names:

| Public module | Selected tap |
|---|---|
| `axi4_intf_master_observer` | lite read/write taps |
| `axi4_intf_slave_observer` | lite read/write taps |
| `axi4_intf_master_observer_full` | passive full read/write taps |
| `axi4_intf_slave_observer_full` | passive full read/write taps |

The wrappers contain no register, meter, histogram, or MonBus policy. Their purpose is to preserve existing consumers while giving synthesis and new integrations explicit top-level names.

### 4.2 Passive full-monitor taps

`axi4_rd_monfull_snoop` and `axi4_wr_monfull_snoop` adapt observed AXI channel signals to `axi_monitor_filtered`. They contain no AXI endpoint or skid buffer. Both master and slave observers use the same read or write adapter because the monitor consumes the same abstract command/data/response events in either role.

Each adapter receives the actual valid and ready for every observed phase. Command admission is based on the actual command handshake, not a wrapper-generated ready. `block_ready` is not connected to any observed valid or ready.

The write adapter preserves the existing full monitor's `USE_WDATA_ORDER_Q` and banking behavior. The read adapter preserves same-ID response attribution. Both adapters expose the status needed by the existing observer telemetry:

- busy and active transaction count
- emitted completion and error counts
- refused command count
- dropped event count, tied to zero unless the full monitor has a real event-loss source to count

### 4.3 Observation-loss accounting

Add an explicit command-refusal event at the transaction manager, where command headroom and same-ID pending state are known. A refusal is an actual observed command handshake that neither allocates nor merges into a pending command entry because the command-entry cap prevents admission.

Each passive tap aggregates refusal events into a saturating 16-bit counter. Reset and `cam_clear` establish an empty, loss-free monitoring epoch. The counter must not increment for:

- a command held valid without an actual ready handshake
- a command merged with an existing same-ID pending entry
- an ID intentionally excluded by the observer's ID-slice filter
- a command admitted after capacity becomes available

The existing observer `TAP_BLOCKED` logic consumes the refused count. Full-variant tests must demonstrate that a saturated monitor continues to observe bus traffic without influencing it and reports the resulting coverage loss.

### 4.4 Capability reporting

The shared core supplies capability bits from the selected monitor family. Full variants use their `TAP_ENABLE_*` parameters for the corresponding full reporter cones. Lite variants retain the current behavior in which performance and debug capability bits read zero because those cones are not present in `axi_monitor_lite`.

`OBS_CAPS1` and `OBS_CAPS2` retain their current meanings, including bank count and total transaction capacity.

## 5. Measurement Plan

### 5.1 Reproducible baseline

Implement and verify the shared observer structure, public full variants, passive taps, and refusal accounting before optimizing full-monitor internals. Run the baseline synthesis matrix on this checkpoint and commit the source state with a named-path commit. Record the commit hash in the characterization document and tracker entry.

This baseline may contain only the changes needed to instantiate the existing full monitor correctly as a passive observer. It must not contain CAM, transaction-manager, reporter, timeout, or timestamp optimizations.

### 5.2 Configurations

Use the same synthesis flow and constraints for every before/after pair.

**Full-feature OOC profile**

- Both master-full and slave-full observer tops
- `MAX_TRANSACTIONS=16`
- `NUM_BANKS=1`
- Error, timeout, completion, threshold, performance, and debug cones enabled
- `N_ADDR_RANGES=4`
- Kintex-7 `xc7k325tffg900-2`, 6.667 ns
- Artix-7 `xc7a100tcsg324-1`, 10.0 ns

**Deployment-shaped profile**

- `axi4_intf_master_observer_full`
- `MAX_TRANSACTIONS=64`
- `NUM_BANKS=4`
- Existing observer cone defaults
- Same two parts and constraints

**Lite context**

Synthesize `axi4_intf_master_observer` in the deployment-shaped profile on both parts. Do not create a lite row for the full-feature profile because the lite monitor lacks its performance and debug cones. Label lite rows as non-feature-equivalent context; never subtract a lite row from a full row and call the difference an optimization improvement.

### 5.3 Metrics and reports

For every row record:

- LUT, FF, LUTRAM, and BRAM counts
- register-to-register WNS and failing endpoint count
- unrouted-net count and synthesis/route status
- hierarchical utilization deep enough to identify monitor CAM, transaction manager, timeout, reporter, and shared observer infrastructure
- worst-path startpoint, endpoint, logic levels, and named cone

Publish full-before/full-after deltas only between identical profiles and parts. Include absolute optimized values as well as deltas. Note placement variation when a small WNS change does not correspond to a changed critical cone.

## 6. Optimization Method

Optimization begins only after the baseline is green and measured. Hierarchical utilization and the worst register-to-register path select each candidate. Initial areas to inspect are:

- asynchronous reset and clear fan-out on CAM IDs and payloads
- wide per-slot transaction update cones
- transaction timestamps and field widths, including proof that any removed field is unused
- the reporter's local transaction-table copy and its reset/update cost
- serial priority encoding, age comparison, and allocation trees
- parallel-read state incorrectly assumed to be RAM-shaped

These are investigation candidates, not mandatory edits. Parallel CAM reads generally require flops; a RAM attribute that Vivado ignores or that increases LUTs without reducing FFs must be reverted. Reset removal requires validity-qualified read review and directed clear/reuse/stale-data tests.

Each candidate follows this sequence:

1. Capture the relevant baseline hierarchy and timing path.
2. Add or identify a test that fails when the candidate behavior is broken.
3. Make one coherent edit without unrelated cleanup.
4. Run targeted tests and the applicable formal/equivalence evidence.
5. Repeat the identical synthesis row.
6. Keep, revise, or revert based on the measured result and verification evidence.

Use golden-reference simulation or formal equivalence for nonlocal or combinational rewrites. The unoptimized full monitor is the reference; lite monitors are not acceptable references for full-only features. Record rejected experiments with their numbers and reason.

## 7. Verification Plan

### 7.1 Passive full taps and observers

Reuse `AXI4IntfObserverTB`, the existing AXI BFMs, and the existing observer test structure. Add full-variant coverage for:

- register reset, round-trip, and truthful capability reporting
- read/write traffic and all full packet classes
- performance-window start/end and debug events
- address-range match and error flavors
- observed-bus conservation while MonBus is stalled
- continued external handshakes under table saturation
- exact refused-command counts and no false refusals
- same-cycle write address/data and write-order queue behavior
- `cam_clear`, slot reuse, mid-run reset, and reissue
- sustained and throttled consumers
- latency histogram sample-loss behavior shared with the lite variant

A saturation test must count accepted commands on the observed wires independently of monitor outputs. It must prove both properties: external traffic continues and monitoring loss is reported.

### 7.2 Optimization regression evidence

For each retained full-monitor optimization:

- Run directed clear/reuse and mutation-sensitive tests for the changed state or cone.
- Compare pre-optimization and post-optimization packets under identical seeds and configurations.
- Run relevant existing full-monitor formal harnesses; add bounded properties for new refusal accounting and for any rewritten handshake/allocation logic.
- Require all formal covers intended to be reachable to reach a non-vacuous witness.
- Run clean FULL AMBA and misc regressions at completion using `source env_python`, `clean-all`, and the area Make targets, never bare pytest.
- Re-run existing lite observer tests to demonstrate that shared-core restructuring did not alter them.

If a full-monitor change affects shared transaction types or producers, include every affected monitor in the same verification and regression scope.

## 8. Documentation and Delivery

The final delivery contains:

- shared observer cores and four thin public wrappers
- two passive full-monitor tap modules and their filelists
- full-variant DV and refusal-accounting formal/test coverage
- a committed unoptimized baseline and subsequent measured optimization commits
- a characterization document with the complete before/after tables and reproduction commands
- tracker updates naming retained wins, rejected experiments, residual timing misses, and verification results
- handbook updates only for durable lessons demonstrated by this work

The final recommendation must distinguish three questions:

1. How much did the full monitor improve against its own baseline?
2. Does it meet the selected FPGA timing targets?
3. Is its remaining cost justified when full-only features are required?

A residual timing miss must be reported plainly. A correct full variant with no measured improvement is a valid negative result, not a reason to hide the baseline or weaken the tests.

## 9. Acceptance Criteria

The work is complete when:

- Both new full observer variants pass their functional and passivity tests.
- Existing lite observers and project integrations remain unchanged in behavior and pass their regressions.
- Full-before/full-after synthesis rows exist for every profile/part pair, with no missing or silently skipped rows.
- Every retained optimization has verification and measurement evidence; every rejected candidate has a recorded disposition.
- Relevant formal proofs and clean FULL AMBA/misc regressions pass, or any external blocker is explicitly isolated and the affected work remains open.
- Documentation reports absolute values, deltas, critical paths, residual failures, and reproduction commands without presenting lite as a feature-equivalent control.
