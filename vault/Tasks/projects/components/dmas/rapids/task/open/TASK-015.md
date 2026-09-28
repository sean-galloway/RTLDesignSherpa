# TASK-015: AXIS monitor-lite in each half (Option B), one arbiter entry per half

**Priority:** P2. Sean's decision 2026-09-27: "Option B" -- the sink-ingress AXIS
monitor lives in `rapids_snk_beats`, the source-egress one in `rapids_src_beats`.
**Status:** open 2026-09-27. Blocked on the `axis4_*_monlite` blocks another
session is writing; rapids-beats is on hold until they land. Filed so the
placement, arbiter widths, config and agent IDs are settled before the wiring
starts and nobody rediscovers them.

## Placement (decided)

| Half | Port monitored | Monitor | Arbiter |
|---|---|---|---|
| `rapids_snk_beats` | `s_axis_*` (ingress, DUT is the AXIS slave) | AXIS slave monitor-lite | half `monbus_arbiter` CLIENTS 2 -> 3 |
| `rapids_src_beats` | `m_axis_*` (egress, DUT is the AXIS master) | AXIS master monitor-lite | half `monbus_arbiter` CLIENTS 2 -> 3 |

The core arbiter (`rapids_core_beats`, CLIENTS 2 = src, snk) and the top do not
change; the top already feeds `core_mon_*` straight into
`monbus_axil4_axil4_group`. This mirrors where the descriptor-read
monitor-lite already lives (inside the scheduler group array), keeps the
"one monitor stream per half" contract, and keeps the half-level tests able to
see the packets. Gate both instances on `USE_AXI_MONITORS`, as the descriptor
monitor-lite is.

## Config and filtering

- The group has three protocol slots (AXI, AXIS, CORE). Its AXIS slot is wired
  to the SRC half's `RDMON_*` registers today (`rapids_beats_top.sv` ~1905),
  which drive nothing else because there is no read-master monitor. Either keep
  that (AXIS filtering configured through `SRC.MON.RDMON_*`) and say so in the
  HAS register map, or add an AXIS block to `rapids_mon_regs.rdl` and regenerate
  through `bin/peakrdl_generate.py` (docs and regmap in lockstep). The
  ISSUE-003 guard (`paddr[11]` in either half) covers either without change.
- Per-monitor enables come from the config block's `cfg_rdeng_mon_*` /
  `cfg_wreng_mon_*` outputs, which currently drive nothing; reusing them for
  the AXIS monitors (rd -> source egress? wr -> sink ingress?) is the least
  register churn, but the names then lie -- rename if reused.

## Agent IDs

In use: descriptor-read AXI monitor 8 (`DESC_AXI_MON_AGENT_ID`), descriptor
engines 16..23, ctrlrd 32, ctrlwr 33, schedulers 48..55. The HAS MonBus page
carries the table. Proposal: sink-ingress AXIS monitor 9, source-egress AXIS
monitor 10 (next to the existing AXI monitor at 8, below the descriptor-engine
block). Add both to the HAS table and to `rapids_pkg` beside the others.

## Verification

- Half-level: `test_snk_data_path_axis_test_beats` / `test_src_...` gain a
  check that an AXIS transfer produces the monitor's packets on `mon_*` with
  the new agent IDs (decode with `TBClasses.monbus.parse`).
- Top-level: `test_rapids_beats_top` monitor cell sees AXIS packets through the
  group's error/capture paths; `test_rapids_beats_top_mon_gate` unchanged.
- Clean full rapids regression (2253 cells at FULL is the baseline at HEAD).
- Harness: a monitors-on build variant if the packets are to reach a tally
  SRAM (separate item; the perf build stays `USE_AXI_MONITORS=0`).
