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

## Working hypothesis for the open defect

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
