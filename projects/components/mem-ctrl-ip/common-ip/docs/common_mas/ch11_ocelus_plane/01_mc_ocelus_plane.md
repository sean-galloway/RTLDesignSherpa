<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->


# `mc_ocelus_plane` — Ocelus observability plane

**Module:** `macro/mc_ocelus_plane.sv`
**Children:** `rtl/amba/ocelus/axi_monitor_lite.sv` (x2), `fub/mc_monlite.sv`,
`rtl/amba/ocelus/monbus_arbiter.sv`, `rtl/amba/ocelus/monbus_axil4_group_1wr.sv`

> Filed as chapter 11 (appended) so chapters 2–10 keep their paths. Added
> 2026-11-01. Granite and pumice instantiate it identically from their cores
> behind `HAS_MON` (default 0); scoria and andesite do not instantiate it.

## Responsibility

Report what the controller is doing, and what went wrong inside it, as
128-bit Ocelus packets written to memory, without being able to stall the
controller:

1. **Port monitors** — two passive `axi_monitor_lite` taps on the core's AXI4
   slave port, one read (AR/R), one write (AW/W/B)
   (`macro/mc_ocelus_plane.sv:196`, `:256`). Error packets (response errors,
   orphan beats, burst length), completion packets with latency, timeout
   packets naming the stuck phase, and threshold packets. The lite never
   touches the traffic it watches: an event it cannot deliver is dropped and
   counted.
2. **Internal events** — `mc_monlite` (`fub/mc_monlite.sv`) turns error and
   debug state the controller already has into `PROTOCOL_CORE` packets
   (`macro/mc_ocelus_plane.sv:310`).
3. **One output** — a 3-client `monbus_arbiter` (`:354`) feeds
   `monbus_axil4_group_1wr` (`:379`), which writes every packet over one
   64-bit AXI-Lite master (`m_axil_*`): packet types picked by
   `cfg_err_select` to the error window as raw 3-beat records (`irq_o` pulses
   per record landed), the rest to the trace window.

At `HAS_MON = 0` the generate's else branch (`:458`) ties every output: the
AXI-Lite master idles with `bready` high and every count reads 0.

## Internal events (`mc_monlite`)

The event code is `mc_common_pkg::mc_event_e`, which is also the event's bit
in `cfg_core_ev_en`. Codes `0x00`–`0x07` are `PktTypeError`, `0x08`–`0x0F`
`PktTypeDebug`.

| code | event | fires on | payload (`event_data`) | tap source |
|---|---|---|---|---|
| 0x00 | `CAL_ERR` | rising | 0 | training plane `cal_err_o` |
| 0x01 | `ZQ_OVERDUE` | rising | 0 | training plane `zq_overdue_o` |
| 0x02 | `REF_BACKLOG` | backlog reaching `REF_BACKLOG_MAX` | `[3:0]` backlog | scheduler plane `dbg_ref_pending_o` (refresh ctrl `pending_refreshes_o`) |
| 0x03 | `AW_RAGGED` | pulse | 0 | AXI plane `dbg_aw_ragged_o` (intake `aw_push_err_o` at the push handshake) |
| 0x04 | `RD_BEAT_LOST` | pulse | 0 | DFI plane `rd_beat_lost_o` (aligner `err_beat_lost_o`, synchronized to `ctl_clk` by `sync_pulse` when `DFI_CDC_EN`) |
| 0x05 | `RET_ORPHAN` | pulse | 0 | AXI plane `dbg_ret_orphan_o` (return ring `err_orphan_o`) |
| 0x06 | `DROPPED` | events were lost | `[15:0]` count | `mc_monlite` itself |
| 0x08 | `INIT_DONE` | rising | `[4:0]` init state | init plane `init_done_o` |
| 0x09 | `INIT_STATE` | any change | `[4:0]` new state | init plane `init_state_o` |
| 0x0A | `DIR_FLIP` | pulse | `[7:0]` batch that ended, `[8]` new dir (1 = write), `[10:9]` cause (0 old-direction fire, 1 drained, 2 batch cap) | `mc_bank_pick` `dbg_dir_*` (0 on FR-FCFS) |
| 0x0B | `REFRESH` | REF / REFpb accepted | `[4:0]` op | scheduler plane `cmd_accept_o` / `cmd_accept_op_o` |
| 0x0C | `ZQ` | ZQCS / ZQCL accepted | `[4:0]` op | same |
| 0x0D | `PAGE_TO_PRE` | page-timeout PRE accepted | 0 | scheduler plane `dbg_accept_to_pre_o` |
| 0x0E | `STORE_FULL` | the store began refusing a push (rising) | `[0]` write side, `[1]` read side | core: `aw_push_valid && !aw_push_ready`, same for AR |
| 0x0F | `RING_FULL` | rising | 0 | core: `!rt_alloc_ready` |

The two contract checks `RD_BEAT_LOST` and `RET_ORPHAN` were simulation-only
assertions before; the fubs now also drive them as synthesizable pulses
(`fub/mc_dfi_rd_aligner.sv`, `fub/mc_rd_return_ring.sv`), the assertions
unchanged beside them.

**Queueing.** Every event has a pending bit; an event sets its bit and
latches its payload, and each cycle the lowest-numbered pending event —
errors first — enters the `gaxi_fifo_sync` output queue if it has room
(`fub/mc_monlite.sv`, the take loop and `w_cap`). The timestamp is
`i_mon_time` at enqueue, a few cycles after the event at most while the
queue drains. A repeat of an event whose bit is still held is lost and
counted; the count leaves as one `DROPPED` packet once nothing else waits,
and clears. Nothing back-pressures the taps.

The plane registers every `ev_*` input once before `mc_monlite`, so all
internal events reach it one cycle late, together, in their original order.
Fed straight from the scheduler's pick, the event detect and drop count made
the worst 100 MHz path on the Artix-7 (granite TASK-008, 17 levels).

`DROPPED` is an Error-class packet (code 0x06 < 0x08), so it counts in
`MON_CORE_STATS.ERRORS`. Under traffic the debug events (direction flips,
page-timeout precharges, refreshes) repeat faster than the plane drains them:
on the board a 64-burst write-then-read pass loses about 340 and sends about
20 `DROPPED` packets. A check that reads `ERRORS` as "real errors" must
disable the `DROPPED` event (`MON_CORE_EV.EV_EN` bit 6). The lost count then
accumulates in `MON_ERR_STATUS.DROPPED` instead of clearing on each report.

**Gating.** `cfg_enable = 0` clears every pending bit and stops new ones;
`cfg_core_ev_en` masks events one by one. The edge detectors keep running
regardless, so enabling the monitor while a level is already high reports
nothing for it.

No head-age starvation event: granite builds `HAS_AGE = 0`, which ties the
age flags off. A starved transaction is caught at the port instead, by the
lite monitors' no-progress timeout (`cfg_timeout_us`).

## Identity and routing

| client | protocol | agent (default) |
|---|---|---|
| read monitor | `PROTOCOL_AXI` | `AGENT_RD` = `0x0010` |
| write monitor | `PROTOCOL_AXI` | `AGENT_WR` = `0x0011` |
| `mc_monlite` | `PROTOCOL_CORE` | `AGENT_CORE` = `0x0012` |

`UNIT_ID` defaults to `0x20` for all three; every id is a core parameter
(`MON_UNIT_ID`, `MON_AGENT_*`). The group's AXI slot filters nothing further
(the port monitors filter inside themselves by `cfg_axi_pkt_mask`); its CORE
slot likewise (`mc_monlite` filters per event); its AXIS slot is unused.
`cfg_err_select` drives both slots' error-select, so one bit per packet type
routes that type to the error window from either protocol.

## Configuration and status

The cores carry configuration and status as `mc_common_pkg::mc_mon_cfg_t` /
`mc_mon_stat_t`; the tops fill them from the `MON_*` CSR block, the same
layout at `0x200`–`0x230` on granite and pumice (`MON_CTRL`,
`MON_LATENCY_THRESH`, `MON_ROUTE`, `MON_CORE_EV`, the four window registers,
`MON_WATERMARK`, and the read-only `MON_ERR_STATUS`, `MON_RD_STATS`,
`MON_WR_STATS`, `MON_CORE_STATS`). Every source resets **off**: the windows
reset to 0, so both must be programmed before a source is enabled. The
generated register documentation is canonical for fields and resets.

## Verification

- `common-ip/dv/tests/fub/test_mc_monlite.py` — every event, edge vs pulse
  behaviour, payloads, `cfg_enable` / `cfg_ev_en` gating (the OFF state),
  priority order, coalesced-repeat drops and the `DROPPED` report.
- `granite-ddr2-lpddr2/dv/tests/top/test_granite_ocelus.py` and
  `pumice-ddr2-lpddr2/dv/tests/top/test_pumice_ocelus.py`, both on the shared
  bench `pumice-ddr2-lpddr2/dv/tbclasses/mc_ocelus_tb.py`: CSRs by name, AXI
  traffic, the writes captured by `MonbusGroupHarness` and decoded with the
  shared parser. `on`: one read and one write completion per burst in the
  trace window, no error or timeout packet on clean traffic, `PROTOCOL_CORE`
  debug records (a direction flip among them) in the error window, irq ==
  records == `MON_ERR_STATUS.REC_COUNT`, the stats CSRs agree. `off`: the
  plane built, every source at reset — nothing written, every count 0.
  Mutation check: tying the read monitor's last-beat tap low fails the
  completion count (`rd=0 wr=2`).
- `HAS_MON = 0` is every other granite and pumice test.
