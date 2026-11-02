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

## Board (2026-11-02, owner: "put granite on the board with light ocelus checks")

- Build knob `GRANITE_HAS_MON=1` (create_project.tcl -> granite_char_top ->
  harness -> macro). The macro answers `m_axil_mon` with a write-ack sink:
  no packet memory, so the checks read the `MON_*` CSRs.
- Host: `bin/seq_ocelus.py`, `make run SEQUENCES="init ocelus"
  RUN_ARGS="--controller granite [--txn N]"`. One write-then-read pass;
  completions == bursts per direction, rd / wr / core errors 0, error-window
  records > 0, mismatched 0; DROPPED reported, not checked. Sim twin:
  `test_granite_char_uart.py::test_granite_uart_ocelus` (HAS_MON=1).
- Timing at 100 MHz (A7 -1) did not close as committed: WNS -5.2 ns, the
  25-level AW-cap path in `monbus_burst_writer`; 75 MHz with that writer
  was -2.5 ns, still in the writer. Fixed in RTL:
  `rtl/amba/ocelus/monbus_burst_writer.sv` pipelines its epoch-start cap
  (two stages, used after two quiet cycles), keeps the in-flight room as a
  down-counter, and runs the no-record-fits fixup off the registered caps
  (-5.2 -> -1.3 ns). `mc_ocelus_plane` registers the `ev_*` inputs (the
  scheduler pick -> drop count path, -1.4 ns). Then closed at 100 MHz with
  Explore: WNS +0.006, WHS +0.021, 43 147 LUT (68.1%); no trims or Pblocks.
  Bitstream `ddr2_char_granite_100mhz_ocelus_pipe3_2026-11-02.bit` (board
  gate scratch).
- Board, that bitstream: smoke (init, write_read, memtest 32/32 over 128 MB)
  pass. Ocelus x3 at 64 bursts: rd/wr completions 64/64, errors 0/0/0,
  records ~31 820, dropped 334-338; at 1000 bursts: 1000/1000, errors 0,
  dropped 6 943. One char windows rep ran clean, mixed_bl8 mismatched 0, wr / rd
  MB/s: defaults 260 / 319, fixed_open_tr2 250 / 236, open_page 262 / 330.
- The first board pass read core errors ~20 a pass. A per-event bisect on
  the board (`MON_CORE_EV.EV_EN` one bit at a time) put them all on
  `DROPPED` reports, an Error-class packet: no real error event fired. The
  host check now leaves `DROPPED` off.
- Writer gates: val/amba 1wr suites 24/24 (full). Mutations: room counter
  not decremented -> 3 fail; pointer fixup disabled -> only
  `axi4_group_1wr[errors_only-256]` fails, so window-wrap coverage is thin.
  On the final RTL: granite top 22 / 1 xfail, pumice ocelus 6, char UART 2.
  STREAM top 40 and RAPIDS top / top_beats / top_g 122 / 36 / 122 ran on the
  first pipelined writer, before the fixup and FIFO-shrink change.

## Not done (follow-ups if wanted)

- A board capture window for `m_axil_mon` (the packets themselves).
- A 1wr test that wraps the window many times (see the mutation above).
- Area trims not tried: group FIFO depths (192 / 96 beats), lite
  MAX_TRANSACTIONS 8.
