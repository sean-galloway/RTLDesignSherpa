# TASK-008 — Ocelus observability on granite and pumice

**State:** closed · **Area:** product-ip/granite-ddr2-lpddr2 (with pumice; the plane is common-ip) · **Opened:** 2026-11-01 · **Closed:** 2026-11-01
**Source:** owner, 2026-11-01: "add ocelus to granite/pumice ... use the single
axil wr port out transmit version", and "make sure internal events use ocelus
for debug/internal error info". Scope agreed: lite monitors, config in RDL
CSRs, RTL + sim (no board harness change).

## What landed

- `common-ip/rtl/macro/mc_ocelus_plane.sv`: two passive `axi_monitor_lite`
  taps on the core's AXI port, `mc_monlite` on internal events, a 3-client
  `monbus_arbiter`, `monbus_axil4_group_1wr` -> one AXI-Lite master
  (`m_axil_mon_*`) writing an error window (3-beat records, `mon_irq_o`) and a
  trace window. Behind `HAS_MON` (default 0) on `granite_core` /
  `pumice_core` and every top.
- `common-ip/rtl/fub/mc_monlite.sv`: `PROTOCOL_CORE` packets, codes
  `mc_common_pkg::mc_event_e` -- errors: cal_err, zq_overdue, refresh backlog
  at max, ragged AW, read beat lost, return-ring orphan, dropped; debug: init
  done / state, direction flip (cause, batch), REF / ZQ issued, page-timeout
  PRE, store full, ring full. Drop-and-count, never stalls the taps.
- New debug taps (unconnected = pruned): `mc_bank_pick` / scheduler plane
  `dbg_dir_*`, `dbg_ref_pending_o`, `dbg_accept_to_pre_o`; AXI plane
  `dbg_aw_ragged_o`, `dbg_ret_orphan_o`; DFI 2.1 plane `rd_beat_lost_o`
  (`sync_pulse` when `DFI_CDC_EN`). The ring's orphan and the aligner's lost
  beat were sim-only assertions; they are synthesizable pulses now as well.
- `MON_*` CSRs at `0x200`-`0x230`, the same block on both RDLs; regenerated
  through `bin/peakrdl_generate.py` (and pumice's DV regmap copy). Every
  source resets off; pumice's reset-parity manifest declares the 20 fields
  (count 98, which also absorbs three fields that had been added earlier
  without moving it).
- Head-age starvation is NOT an event: granite builds `HAS_AGE = 0`; the port
  monitors' no-progress timeout covers a starved transaction instead.

## Evidence

- `common-ip/dv/tests/fub/test_mc_monlite.py`: 5 cells (errors, debug,
  gating incl. the OFF state, priority, drops) -- pass.
- `test_granite_ocelus.py` / `test_pumice_ocelus.py` on the shared
  `pumice-ddr2-lpddr2/dv/tbclasses/mc_ocelus_tb.py`: `on` (completions ==
  bursts per direction, no error/timeout packet on clean traffic, mc_monlite
  debug records incl. a direction flip in the error window, irq == records ==
  REC_COUNT, stats CSRs agree) and `off` (nothing written, counts 0). Mutation:
  read monitor's last-beat tap tied low -> `completions rd=0 wr=2`, fails.
- Regressions, clean: granite top 22 / 1 xfail (func), pumice fub 32, macro
  78, top 222, phy 32 / 4 skipped, common-ip fub 41, macro 36 / 3 xfail
  (after connecting the new pins on the arbiter macro TB), the ddr2 char
  framework (board-gate sim).
- Area, synth-only, `granite_top_geared` (A7 geometry): HAS_MON 0 -> 1 =
  9 189 -> 14 396 LUT, 5 672 -> 9 489 FF. The plane: group 2 097 LUT (core
  1 970), read monitor 1 025, write monitor 1 305, arbiter 312, mc_monlite
  211. The `MON_*` registers cost ~280 FF in the CSR block at HAS_MON 0 too.

## Not done (follow-ups if wanted)

- Board: no char-harness capture window for `m_axil_mon`, no bitstream with
  HAS_MON = 1, no timing measurement of it at 100 MHz.
- Area trims not tried: group FIFO depths (192 / 96 beats), lite
  MAX_TRANSACTIONS 8.
