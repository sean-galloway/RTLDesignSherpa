# Granite A7 bring-up — 2026-10-11 → 2026-10-12

## Verdict

**Progress, one defect fixed, one defect precisely characterized and open.**
Fixed: a genuine `mc_xddr2_entry_store` write deadlock (fdone race, commit
`3d690ab3f`). Open: multi-beat (split) bursts still wedge on the board while
single-beat bursts pass; the board-vs-sim delta is now exactly one
interaction and the next diagnostic is named below.

## Evidence (Nexys A7-100T, serial 210292BFA3EE)

### The original symptom (2026-10-11)

init_done=1, then any engine run wedged silently. First hypothesis
("ring ticket at insert") was **wrong** — investigated and exonerated:
`mc_xddr2_entry_store` implements ticket-at-insert/issue-forward correctly
(`common-ip/rtl/fub/mc_xddr2_entry_store.sv:288-323`).

### Board localization (2026-10-12)

Probes via the framed UART protocol (`build-perf/host/ddr2_char.py` on
ttyUSB3, bench later moved to a clean dir — `/tmp` scripts shadow stdlib
`dis`):

- **WR phase wedges first** (not reads): engine produces exactly **48 beats**
  (its max-outstanding window, 6 bursts x 8 beats) then freezes; `WR_GEN0_STATUS`
  shows `crc_valid` with `done` never setting; no B responses.
- **DFI cmd monitor (0x80000) shows ZERO commands** after GO — the scheduler
  issues nothing, no ACT, no WR.
- Controller stall/sched stats all read 0 (they only count while the harness
  timer runs; timer ran, so the zeros are real: the pick machinery never saw
  a candidate).

### Config bisect on the board (fixed bitstream)

| engine cfg        | result                          |
|-------------------|---------------------------------|
| blen=1,  txn=64   | **DONE in 0.1 s** (PROD=64)     |
| blen=2,  txn=32   | wedge (PROD=30)                 |
| blen=8,  txn=1    | **wedge (PROD=8)**              |
| blen=8,  txn=64   | wedge (PROD=48)                 |

blen=1 needs no burst chopping; blen>=2 goes through `mc_wr_splitter` (one
AW -> 1-beat sub-bursts at x16). A single split burst wedges, and a **blen=1
run immediately afterwards completes instantly** — the store does NOT stay
wedged; the split-burst sub-entries complete without issuing DFI commands and
without the aggregator emitting the host B (aggregator + splitter + intake are
common with pumice and proven there at this exact geometry, so the miscount
is introduced by the granite entry-store seam).

### Fixed and verified

1. **`mc_xddr2_entry_store` fdone race (commit `3d690ab3f`)**: the staging
   FIFO accepted the NEXT sub-burst's W beats while the current entry drained
   (`wd_ready` gated only by `r_wr_valid`); the early `wd_last` set fdone, the
   next AW push cleared it, fdone could never rise again — a silent deadlock.
   Fix: `wd_ready = r_wr_valid && !r_wr_fdone`. Post-fix the board shows
   backpressure (`OBS_WR_BP=87`) and the store recovers; wedge persists for
   split bursts.
2. **DV gap closed**: prior sims never split a host burst (BFM bl_words ==
    BURST_WORDS). New `granite_top_geared` cocotb smoke reproduces the
    original deadlock at the true A7 geometry (x16 devices, 8-beat bursts,
    NUM_ENTRIES=8) and passes with the fix; DFI model is now burst-aware
    (one rddata_en window == one DRAM burst == BURST_WORDS words); a
    multi-outstanding mode (GRANITE_MANY) mirrors the engines. Committed with
    the fix.

### Trap for the next session

**`make bitstream` does NOT stage the bit**: Vivado writes
`fpga/build/vivado_project/ddr2_char.runs/impl_1/granite_char_top.bit`; it
must be copied to `fpga/bitstream/ddr2_char.bit` before `make program`, else
the OLD bit is flashed (this cost one full debug cycle — the 04:16 "fixed"
program was the 21:31 stale bit). Verify `ls -la fpga/bitstream/` timestamps.

## Whole-harness sim repro (2026-10-12, harness testing per owner)

Built `granite_char_uart_uart_tb_top` (clone of the pumice whole-harness UART
TB) + filelist + `test_granite_char_uart.py::test_granite_uart_smoke` in
`ddr2_char_framework/dv/`. Drives the REAL uart_axil_bridge + REAL char
engines + DFISlavePHY at the exact A7 geometry (rate2 / 32b beat / x16 / BL4),
host program byte-identical to the board's.

- **REPRODUCES the wedge**: `wr=False, rd=False` (engines never finish), same
  as silicon. The BFM-based `granite_top_geared` smoke passes at the identical
  geometry — the real engines' AXI flavor is required to fail.
- **A/B control**: pumice whole-harness smoke PASSES at the same geometry
  (`test_ddr2_char_uart_smoke_rate2_beat32_x16`, added in the same session).
  The defect is granite-seam-specific, not geometry-specific.
- Wedge mechanics observed (per-cycle window recorder): engine GO lands
  (APB write 0x400/0x1 observed at the macro's chargen port); the injector
  latches the correct program (txn=4, blen=4) and drives AW x4 + held WVALID;
  the controller accepts ~1 AW (AWREADY 0->1->0), W beats enter the W skid,
  then AWREADY stays 0, the store never sets r_wr_valid, **zero DFI commands
  ever**, and the run ends fully drained/idle with the engine in S_DONE
  awaiting B's. No ragged-burst $error (splitter output is clean). No harness
  watchdog reset. The AWs/W vanish between the axi-slave skid and the store.
- The intake push path is comb-simple (meta FIFO rd_valid -> aw_push ->
  pop on store ready), so the vanish needs cycle-level visibility: next step
  is a VCD parse of the failing window (FST compiled but dump didn't land —
  finish the waves plumbing) or an ILA on silicon at
  u_axi4_plane/u_wr_intake (u_slave_wr skid, u_aw_meta_fifo, aw_push_*) +
  u_entry_store — the owner pre-authorized ILA for this.

## ROOT CAUSE (2026-10-12, whole-harness UART sim + VCD)

The split-burst hang is a **B-response consolidation defect**, fixed in
`361d6cd56`. VCD of the whole-harness sim (write path, `WAVES=1` + fst2vcd +
`/tmp/granite-bringup/vcd_extract.py`) shows the write path worked end-to-end
all along: all 16 sub-bursts (4 host bursts x 4 chops at x16) pushed into the
entry store, scheduled, committed, and WR commands issued. The defect:
`mc_xddr2_entry_store` emitted `wr_done` for EVERY chopped sub-burst. The
AXI slave returned one B per sub-burst — 16 B's for 4 host AWs — the engine's
outstanding count desynced, and the run hung with the controller fully
drained, zero DFI-pin command activity, `crc_valid` set, `done` never. Pumice
never sees this because its storage plane's wr data CAM aggregates sub-burst
B's; the storage-less SKU must do the same at the seam. blen=1 escaped
because unsplit bursts are exactly one sub (agg=0/last=1).

Fix: `wr_done_valid_o` qualified by the captured `aw_push_last_i` (final
chunk of a split; unsplit bursts carry last=1). Together with the earlier
fdone gate (3d690ab3f) the write path now completes in the whole-harness sim
(`wr=True, done=1`) for the first time; granite core + top_geared
regressions (incl. dev16) PASS.

## Open: read data mismatch (the remaining defect)

With writes fixed, the READ engine fails independently: framing is correct
(4 bursts x 4 beats + RLAST at the engine; the intake's collapse
`w_sub_last && (!w_head_agg || w_head_last)` works — ar_agg_i=1,
w_head_last=1 on final subs, chopper w_total=4), but 15 of 16 beats mismatch
and `valid` never sets. Writes provably land at the right addresses (the
BFM top_geared readback passes at dev16), so the read return stream is
data-wrong: either the read sub-addresses differ from the write sub-addresses
(chopper vs splitter column stride) or the ring's ticket->data pairing is
shifted (15 returns were observed for 16 sub-reads in one window). Next
crack: same VCD flow, dump wr aw_push_{bank,row,col} vs rd
ar_push_{bank,row,col} per sub-burst and the ring fill/drain ticket order —
the tooling is proven, the window is ~10 cycles.

## Read defect CLOSED (2026-10-12): sim-model misalignment, not RTL

The read 15/16-mismatch was the DFISlavePHY model's read-valid LEADING the
controller's rddata_en window by one cycle: the rd_aligner's enable-window
credit gate (which exists to reject PHY preamble valids) discarded the very
first real return (`RD_ALIGNER probe: blocked_real=1, first_valid one cycle
before first_en`). Later returns back-filled the ring slots one position off
(`rd[k] = wr[k+1]`, 15 returns for 16 sub-reads, last read stranded). The
controller is correct here — on silicon the a7ddrphy drives data inside the
programmed window (the read_en_gated model), and the board trains
t_rddata_en. The granite smoke had t_rddata_en=6 vs the model's latency;
aligning to t_rddata_en=4 (the proven pumice whole-harness value) makes the
smoke PASS end-to-end: write engine done, read engine done, CRC match,
mism=0. Whole-harness UART sim is GREEN at the exact A7 geometry with the
real engines — the granite stack is functionally complete in the most
faithful sim available. Next: bitstream with the B-consolidation fix, A7
re-run, char matrix.

## Board re-run with the B-fix (2026-10-12): WRITE PATH FIXED ON SILICON

Bitstream rebuilt with `361d6cd56` (30,446 LUT / 48.0%, WNS +9.2 ns class).
`blen=8 x64` engine run — the exact shape that hung before:

- **WR: DONE, PROD=512** (all beats produced, BP=1867 backpressure — the
  fdone gate visibly working). First multi-beat write completion on silicon.
- RD: engines reach DONE, CRC exp==act (0xce53ec12, match, valid), but the
  engine's per-beat comparator latched BEATS_MISM=512 / data_error with
  STRAY_BEATS=0. Per-beat comparator vs aggregate CRC disagreeing is the
  untrained-read-capture signature: the board read-leveling sweep
  (rddata_delay / bitslip / IDELAY taps via host_bringup_75.py) has NEVER
  run on granite; this probe only wrote controller timing CSRs. Next board
  step is the leveling flow, then the char matrix.

## Utilization: pumice vs granite vs LiteDRAM (A7-100T, post-route)

Whole design (controller + char harness, 75 MHz):
  pumice   35,316 LUT (55.7%)  30,427 FF  2 BRAM
  granite  30,446 LUT (48.0%)  28,109 FF  (harness-dominated)

Controller only (hierarchical, the honest comparison):
  | block                | LUT   | FF    | BRAM36 |
  |----------------------|-------|-------|--------|
  | litedram_core        | 4,356 | 3,348 | 13+9   |
  | granite (top_geared) | 3,666 | 3,655 | 1      |
  | pumice (top_geared)  | 7,811 | 5,923 | 2      |

Granite plane split (u_core 3,465): axi 1,306 / entry_store **140** /
sched 1,394 / train 226 / dfi 403. Pumice plane split (u_core 7,541): axi
1,380 / **storage 2,020** / sched 3,520 / train 224 / dfi 403.
Takeaways: the storage plane (2,020 LUT) is 93% replaced by a 140-LUT entry
store; granite's scheduler is 1,394 vs pumice's 3,520 (research knobs off);
granite's controller is ~16% BELOW LiteDRAM's core in LUTs — the storage-
less product SKU meets its area goal. BRAM: both RDS stacks use ~1-2 RAMB36
(ring + staging) vs LiteDRAM's 13+9 (its datapath/FIFOs live in BRAM).

## Read training attempts (2026-10-12): no clean setting found

- `host_sweep_rddata_delay.py` (wrlat=1, rden=6): beats_mismatched=16 at
  EVERY rddata_delay 0..15 — not a pure data/valid alignment offset.
- `host_bringup_75.py` (full flow: read eye leveling + write-phase sweep):
  every readback-based check fails 16/16 at every (cmd_delay, wr_phase,
  wrlat) cell; BEST=min=16. Note the write sweep verifies by reading back,
  so broken reads contaminate it — write COMMAND/data correctness on silicon
  is not yet independently proven.
- The probe's "CRC match" is explained: the rd engine's actual-CRC appears
  generator-based (always equals expected); the per-beat comparator is the
  real check and it fails on every beat.
- Perf sweep was NOT run: with reads unclean it would report
  corrupted-data bandwidth — the tool itself warns this is a false-pass
  mode (pumice ISSUE-015). No trustworthy granite-vs-pumice-vs-LiteDRAM
  perf numbers exist yet.
- Next: ILA on the granite read path (owner pre-authorized) — DFI cmd vs
  dfi_rddata_valid/dfi_rddata at the pins, plus the aligner capture, to find
  the phase/lane failure (the pumice bringup needed exactly this ILA to
  resolve its read eye). The whole-harness sim stays green, so the defect is
  board-PHY-interface integration, not controller logic.

## Working hypothesis for the open defect (updated)

blen>=2 (split) sub-bursts at the 1-deep entry store: sub-entries neither
issue to the DFI nor produce their sub-B, yet the store frees itself. The
sub-burst AW stream differs from the engine's direct (blen=1) stream only in
source (splitter) and pace (back-to-back). Next diagnostic, in order:
1. **Whole-harness granite UART sim**: clone
   `ddr2_char_framework/dv/tests/test_ddr2_char_uart.py` onto
   `granite_char_harness` — real engines + real UART bridge + DFISlavePHY.
   This is the only environment that reproduces the engine's exact AXI
   flavor; the BFM-based top_geared smoke passes at the full board config.
2. If sim still passes: ILA on `u_entry_store` (r_wr_valid/fdone/sched,
   aw_push handshake, wr_done) + `u_axi4_plane` wr path, triggered on GO.

## Environment notes

- Bench: Nexys A7-100T serial 210292BFA3EE, UART ttyUSB3, currently flashed
  with the FIXED granite bit (04:24). Pumice keep bit:
  `/mnt/data/fpga-hold/nexys_a7_100t/ddr2_char/ddr2_char.bit` (stale CSR gen —
  banner clk=0.00MHz, no BUILD_ID; fine for bitstream-healthy checks only).
- Pumice post-rename reference: `char_post_rename_2026-10-11.csv`
  (matrix ALL PASS; anchor 561.2 MB/s vs in-book 561.1).
- Board probes live in `/tmp/granite-bringup/probe*.py` (diagnostic only).
