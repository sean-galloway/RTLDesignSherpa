# TASK-015: AXIS monitor-lite in each half (Option B), one arbiter entry per half

**Priority:** P2. Sean's decision 2026-09-27: "Option B" -- the sink-ingress AXIS
monitor lives in `rapids_snk_beats`, the source-egress one in `rapids_src_beats`.
**Status:** CLOSED 2026-09-27 (closing note at the end); was open 2026-09-27,
blocked on the `axis4_*_monlite` blocks another session was writing (landed as
amba 2e63ba799). Filed so the placement, arbiter widths, config and agent IDs
were settled before the wiring started.

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

---

**CLOSED 2026-09-27.** Implemented as decided (Option B):

- `rapids_snk_beats`: `axis4_slave_monlite` between `s_axis_*` and the sink data
  path (agent `AXIS_MON_AGENT_ID` = 9); `rapids_src_beats`: `axis4_master_monlite`
  between the source data path and `m_axis_*` (agent 10). `USE_MONITOR` follows
  `USE_AXI_MONITORS`; the wrapper's `axis4_slave` / `axis4_master` skid stage
  (depth 4) sits on the network port in EVERY build, the same way the descriptor
  monlite carries the `axi4_master_rd` skids. Each half's `monbus_arbiter` went
  from 2 to 3 clients (array, AXIS monitor, placeholder). Core arbiter and top
  egress unchanged.
- Config: new `cfg_axis_mon_*` ports on the halves and core (`src_`/`snk_`),
  fed at the top from the config block's previously dangling outputs: SRC
  `cfg_rdeng_mon_*` (so `SRC.MON.RDMON_*` programs the source-egress monitor)
  and SNK `cfg_wreng_mon_*` (`SNK.MON.WRMON_*` programs the sink-ingress one).
  The config block gained `cfg_*_mon_compl_enable` (the `COMPL_EN` bit was
  declared but never driven out). Class map: error/channel/strb <- ERR_EN,
  compl <- COMPL_EN, credit/stream <- PERF_EN, timeout <- TIMEOUT_EN; `*_TIMEOUT`
  low 16 bits are microseconds, `*_LATENCY_THRESH` the stall-cycle threshold.
  New params `ACLK_MHZ` (microsecond tick), `SNK/SRC_AXIS_MON_AGENT_ID`
  threaded core -> top. Status counts are half/core outputs, unconnected at the
  top (no register yet).
- Found on the way: rapids BUG-008 -- PKT_MASK was documented "1 = enable"
  while the lites and the group mask on 1. Description corrected and registers
  regenerated; the all-masked reset (0xFFFF) is as intended (Sean, 2026-09-28),
  so a host must clear the classes it wants. STREAM's register file carries the
  same description (stream BUG-016, description-only).
- Filelists: the two wrapper filelists added to both half filelists and the core
  filelist (the loader dedups).
- Verification: `rapids_core_beats_tb` decodes every merged monbus packet with
  `TBClasses.monbus.parse` and both directional tests require one
  Completion/STREAM_END per AXIS packet with the channel's tid and beat count
  (the source egress cuts a descriptor into drain-size packets, `m_axis_tlast`
  per drain burst, so it reports `beats / drain_size` completions). New top
  cell `test_rapids_beats_top_axis_mon` programs both monitors over APB and
  decodes the raw 24-byte trace records the group's capture master writes
  (`parse_stream`), requiring the same completions from agents 0x09 and 0x0A.
  `test_rapids_beats_top_mon_gate` (monitors off) unchanged and green. The
  half-level data-path tests cannot see the monitor (it lives in the half, not
  the data path), so the core and top are where it is checked.
- Lint: Verilator on `rapids_beats_top`, 626 warnings vs 629 at HEAD, no
  errors (the change removes three dangling-output warnings and adds none).
- Docs: MAS top / config-block / register pages, the port list regenerated
  (324 ports), HAS block diagram, MonBus agent table (0x09/0x0A live) and
  register map (roles, DROP-mask polarity).
- Regression (clean, `make clean-all` then `make run-all-full-parallel`),
  2026-09-28: fub 162/162, fub_beats 1275/1275, macro 36/36, macro_beats
  747/747, top_beats 36/36 (33 + the three levels of the new cell) -- 2256
  cells green. The top_beats area was re-run clean after a test-only fix (the
  new cell first counted raw capture beats and stopped before the sink's
  record had drained; it now waits for the expected completions and a quiet
  stream); the RTL was identical across both runs.
- Side findings filed: rapids ISSUE-005 (scheduler / descriptor-engine
  completions ignore `SCHED_CONFIG.COMPL_EN`; visible now that packets pass the
  group), stream BUG-016 (the same PKT_MASK inversion in STREAM's register file).
