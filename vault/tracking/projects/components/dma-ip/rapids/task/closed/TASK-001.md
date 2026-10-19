# TASK-001: adopt the shared instrumentation pair (axi4_intf_master_observer + dma_slave_monitors)
> **Was `RAPIDS-OBS` until 2026-09-24.** Renamed when this area adopted per-lane ID sequences. Older references, commit messages and handbook notes use the old ID.

**Status:** CLOSED 2026-09-27 — both observers adopted on the Genesys 2 harness and the
STREAM five-knob characterization measured through them (perf report v1.2, section 7):
line rate on all four ports at 8 ch x 256 KB (99.4 / 100 / 100 / 100 %), knees at 4-beat
bursts and ~64-96 cycles of memory latency, 67/67 configurations golden-clean. The
campaign also found and closed rapids BUG-003 / stream BUG-011. The 2026-09-24 close
below stands as history: it dropped adoption on a cost basis the observers no longer have.

## Reopened 2026-09-27: the cost basis changed, and the AXIS half never existed

Two things moved since the close:

1. **The observers were re-taped onto `axi_monitor_lite`** (misc `78cddb5e2`).
   The +4223 LUTs measured below were monitor CAM taps and their timer pools; the
   lite has neither. On the stream build-obs bitstream the swap took the observer
   pair from 184,047 to 71,671 LUTs (-61%) with per-iteration monbus class counts
   unchanged. The rapids number below is stale and must be re-measured, not argued
   from.
2. **`axis4_intf_observer` now exists** (`projects/components/utility-ip/misc/rtl/`, same
   `obs_regs` map, same monbus egress, `axis_bus_meter` inside, PROTOCOL_AXIS
   packets in all six AXIS classes). There was no AXIS observer to adopt before;
   the harness's two bare `axis_bus_meter` instances (`u_meter_sin`, `u_meter_sout`)
   are what it replaces on the stream side.

Scope now: wrap the rapids harness's AXI4 master read/write ports with
`axi4_intf_master_observer` and its `s_axis_*` / `m_axis_*` with
`axis4_intf_observer`, behind a knob mirroring stream's `OBS_ENABLE_MON_TAPS`; keep
`USE_AXI_MONITORS` / `GEN_MON` as they are; synth the lite-based pair and record the
delta against the 60,651 / 65,974 / 71,721 LUT points measured 2026-09-27 for
bare / lite / full in-core monitors. The latency histogram the close called out as
"a real capability" comes with the AXI observer.

## Implemented 2026-09-27 (harness wiring)

`flows-rapids-beats/rtl/rapids_char_harness.sv`, additive and default OUT:

- Knobs `USE_OBSERVERS` (build both observers) and `OBS_ENABLE_MON_TAPS` (arm
  their monbus event taps), plumbed like `USE_AXI_MONITORS` / `GEN_MON`: harness ->
  `rapids_char_top` -> `rapids_char_genesys2_top`, `create_project.tcl` env generics,
  `Makefile` exports + help, `dv/test_rapids_char_harness.py` (`TEST_USE_OBSERVERS`,
  `TEST_OBS_ENABLE_MON_TAPS`). `USE_AXI_MONITORS` / `GEN_MON` untouched.
- New host region `REGION_OBS = 4'h3` (`addr[19:16]`): the one `apb4_master` fans
  out by region -- the DUT keeps `REGION_APB` and every kick; region 3 goes to the
  observers, `paddr[12]` = 0 the AXI observer, 1 the AXIS observer, each a 4 KB
  `obs_regs` map. Not built: PREADY with PSLVERR and 0, so the host can tell.
- `u_obs_axi` = `axi4_intf_master_observer` on `rd_*` / `wr_*` (NUM_CHANNELS=8,
  rid map = identity since rapids puts the channel id in the low ID bits,
  `WR_CH_FROM_AWID=1`, latency histograms on, `MAX_TRANSACTIONS=64`, lite taps
  gated by the knob). `u_obs_axis` = `axis4_intf_observer` NUM_PORTS=2: port 0
  `s_axis` (sink ingress), port 1 `m_axis` (source egress), per-tid buckets.
  Both on `obs_meter_clear` / `obs_meter_freeze` (the GO-armed window) and
  `cam_clear`; monbus egress into always-accept AXIL responders, as `m_axil_mon_*`.
- The bare `axi_bus_meter` / `axis_bus_meter` instances and the region-2 `OBS_*`
  CSRs stay: `run_characterization.py` / `dump_status.py` read those and are
  unchanged. Reading the observers from the host is a follow-up (by name through
  `obs_regs_top_regmap.py`, region 3).
- Filelist `flists/rapids_char_harness.f` pulls both observer filelists (their
  closure must compile in every build; the instances are generate-gated).
- Docs: `rapids_char_guide` ch02 (region table + knob paragraph) and ch05 (region
  table).

Lint (`rapids_char_genesys2_top`, the matrix recipe): 0 errors at (0,0), (1,0),
(1,1).

## Measured 2026-09-27 (Genesys 2, XC7K325T, 8ch, 100 MHz, synth-only)

verify-sim (the harness sink self-check) PASSES with the observers compiled out
(5:09) and with both built plus taps armed (6:22): attaching them does not change
the DUT's result. Synth, one run each, `create_project.tcl` generics confirmed
bound in the Vivado log:

| variant | LUTs | regs | WNS (synth) |
|---|---|---|---|
| bare (shipped: no in-core monitors, no observers) | 60,651 | 43,144 | +3.683 |
| USE_OBSERVERS=1, taps off (meters + latency histograms + regs + egress) | 71,594 | 55,433 | +3.703 |
| USE_OBSERVERS=1, OBS_ENABLE_MON_TAPS=1 (lite taps armed) | 79,384 | 63,454 | +0.869 |

So the pair costs 10,943 LUTs (+18%) as instruments and 18,733 (+31%) with the
event taps, against the +4,223 the close below measured for ONE observer on the
full monitor at its smallest legal config. Timing closes in every variant; the
taps take 2.8 ns of the synth margin, which is where an implementation run
should look first if a tapped bitstream is ever wanted. The shipped bitstream
(both knobs 0) is byte-for-byte the bare configuration.

Not done, on purpose: no bitstream, no board run (the observers are default OUT
and the user scoped this to building them); the host tools do not yet read
region 3 (`obs_regs_top_regmap.py` by name is the path, as the stream host does).


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
