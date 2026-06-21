# Trackers

Passive monitors for the ddr2-lpddr2 controller's internal FUBs.

A tracker:
- Attaches as a `cocotb.start_soon(tracker.run())` background task.
- Snoops the FUB's external outputs every clock cycle.
- Decodes activity into typed event records (dataclasses) stored in `deque`s.
- Provides `.stats()` and compliance-check methods for use in scoreboarding.
- **Never drives anything** — observation only.

## Available trackers

| Tracker | Observes | Useful for |
|---|---|---|
| `SchedulerTracker` | `scheduler.sv` external bus: `cmd_*`, `evt_*`, grants, `wr/rd_issued_*` | Replay debug, op-distribution coverage, W/R balance, init/refresh priority compliance |
| `RefreshTracker` | `refresh_ctrl.sv` outputs: `refresh_req_o`, `pending_refreshes_o` (+ scheduler `refresh_grant_o`) | JEDEC tREFI compliance, postponed-refresh JEDEC-8 check, request-to-grant latency |

## Usage

```python
from tbclasses.trackers import SchedulerTracker, RefreshTracker
import cocotb

# In a cocotb test or TB setup:
sched_tr = SchedulerTracker(dut)
refr_tr  = RefreshTracker(dut)
cocotb.start_soon(sched_tr.run())
cocotb.start_soon(refr_tr.run())

# ... run the test ...

# Inspect:
print(sched_tr.stats())
# {'total_cmds': 42, 'op_counts': {'ACT': 7, 'WRA': 4, 'RDA': 3, 'REF': 1, ...}, ...}

print(refr_tr.stats())
# {'total_grants': 1, 'max_pending_refreshes': 3,
#  'jedec_postpone_violation': False, ...}

assert not refr_tr.jedec_postpone_violation()
```

## Suggested follow-on trackers

If we add more tracker files in this directory, the most useful would be:

| Tracker | Why interesting |
|---|---|
| `XBankTimersTracker` | Per-(rank, bank) state transitions, tRC/tRAS/tWR margin tracking, row-hit rate. The bank state diagram is the densest state in the controller. |
| `PagePredictorTracker` | Per-bank counter history, predict_open transitions, hit/miss rate. Validates HAPPY heuristics under real traffic. |
| `DfiCmdFormatterTracker` | JEDEC truth-table compliance check (DDR2 ras_n/cas_n/we_n combos). ODT timing validation. |
| `PowerdownTracker` | Active/APD/SR/DPD state transitions, CKE timing, residency stats. Critical for power-mgmt verification when E (power management) lands. |
| `WrBeatSequencerTracker` / `RdClAlignerTracker` | Per-op state through the pipelines, latency-per-op, throughput. Critical for verifying C (multi-outstanding) is actually delivering 2x perf. |
| `InitSequencerTracker` | Cold-boot step sequence, MR-write log, init duration. Useful when B (LPDDR2 family) lands and init flow gets memtype-specific. |

## Design conventions

- Sample on `RisingEdge(dut.mc_clk)` then `Timer(1, 'ps')` to settle NBAs (matches the FUB testbench convention in this project).
- Tolerate missing signals via `_safe_int` / `_is_high` helpers — a tracker should not crash a TB that only exposes a subset of ports.
- Events are dataclasses with `sim_time_ns` and `cycle` for cross-referencing waveforms.
- Statistics are computed lazily on `.stats()` rather than maintained incrementally — keeps the hot path cheap.
