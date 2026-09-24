# TASK-001: adopt the shared instrumentation pair (axi4_intf_master_observer + dma_slave_monitors)
> **Was `RAPIDS-OBS` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** CLOSED 2026-09-24 — observer adoption DROPPED on measured evidence; the
real gap it was pointing at (per-channel WRITE attribution) is implemented and verified.

## The observer is not adopted, and should not be

This task carried its own test: *"Check whether the same is true here before
adopting: the argument holds only where the meters are NOT already the shared
blocks."* Checked — and it is already true here.

`rapids_beats_top.sv:646/677` already instantiates `axi_bus_meter` **directly**,
twice: `u_rd_bus_meter` on the read master and `u_wr_bus_meter` on the write
master. That is the same shared primitive `axi4_intf_master_observer` wraps
internally, so the task's stated justification — *"one instrument across
RAPIDS/STREAM/pumice means one definition of a stalled cycle"* — is **already
satisfied**, and the per-direction read/write split it promises is already
delivered by those two taps.

This is exactly the ground on which [[PUMICE-016]] was DROPPED 2026-09-23, with
the cost measured rather than argued: `axi4_intf_master_observer` at its smallest
legal config is **+4223 LUTs / +1185 FFs — +208%** over `2x axi_bus_meter +
2x axi_perf_latency_hist`, and the extra area is monitor CAM taps, `monbus_arbiter`
and a regblock that are *not parameter-removable* and buy no measurement RAPIDS
lacks. One difference from pumice, recorded so nobody thinks the check was
sloppy: RAPIDS has **no** `axi_perf_latency_hist`, so the observer would add a
latency histogram. That is a real capability — but it is not what this task
argued for, and it does not justify the wrapper. File it separately if wanted.

## What WAS missing, and is now done

The task was pointing at something real. `rapids_beats_top.sv` carried an honest
comment: the WRITE per-channel buckets were deliberately left unwired because
`snk_data_path_beats` tied off the write engine's `o_active_channel_id`, so
`u_wr_bus_meter` saw `i_channel_id='0` — *"Populating WRMON_PERF_CH_* from that
would report a fiction; zeros are honestly 'not implemented'."* Correct call, and
the RDL had specified those registers all along.

Fixed by plumbing the sideband the five levels it had to travel — the reason it
was left undone, since STREAM keeps it internal to `stream_core` where the meter
sits in the same module:

    axi_write_engine_beats (already exported it)
      -> snk_data_path_beats -> snk_data_path_axis_beats
      -> rapids_snk_beats -> rapids_core_beats -> rapids_beats_top

`axi_bus_meter.sv:71-73` documents exactly this wiring as the intended source for
the write side (the W bus has no wid). The SNK half now uses **its own**
`SNK.PERF_CH_SEL` selector, symmetric with SRC, and publishes
`WRMON_PERF_CH_PROD_BP` / `_STARV_IDLE` / `_CH_OVERFLOW`. **No RDL change and no
PeakRDL regeneration** — the registers already existed as `sw=r hw=w`.

## Verified

| check | result |
|---|---|
| `verilator --lint-only` whole hierarchy | RC=0, **zero** new warnings (the 3 WIDTHEXPAND in `snk_data_path_axis_beats` cite lines 186/241, outside the edit) |
| NEW `test_rapids_beats_top_perf_ch_readout_wr` | **PASS** — ch0 prod=**4**, ch1 prod=**16**, exactly the beats driven; overflow=0 |
| existing read-side `..._perf_ch_readout` (control) | **PASS**, unchanged (ch0=4, ch1=16) |
| **mutation** — meter reverted to `i_channel_id='0` | **FAILS as intended**: both channels read prod=0, all three assertions fire. Restored, `cmp` clean. |

The mutation is the point: without it a passing test cannot distinguish working
plumbing from a vacuous check. Note the mutated run reads 0/0 rather than
"everything in channel 0" — tying `i_channel_valid` low stops the buckets
incrementing at all; the assertions catch both shapes.

## Stale text corrected alongside

- `dma_slave_monitors` in this task's title is **retired** — module, filelist and
  its `slvmon_regs` regblock all deleted (STREAM TASK-073, 2026-09-20). The
  `-f .../dma_slave_monitors.f` line this entry quoted no longer resolves. The
  slave-side equivalent is `axi4_intf_slave_observer` + `obs_regs`.
- The beats HAS (`ch06_performance/01_throughput.md`) said wiring the observer in
  was *"the remaining step to report measured GB/s"* and still listed
  `dma_slave_monitors` as in use. Both corrected.
