# TASK-007 — narrow AXI beats on the wide host return wrong data back to back

**State:** CLOSED 2026-11-02 · **Area:** product-ip/granite-ddr2-lpddr2 · **Opened:** 2026-10-29
**Source:** found while closing TASK-003 item 6 (the DFI 1:4 proxy's "two
valids per read" was the host driving 8-byte beats on the 128-bit bus).
**Depends on:** nothing; the 1:4 128-bit host build (TASK-003 item 6) is the
geometry that shows it.

## What

On the DFI 1:4 build (`GRANITE_DFI4`: BL8, x16, 128-bit host AXI, one
AXI beat = one DRAM burst) a stream of **8-byte AXI beats** (AxSIZE 3 on a
16-byte bus: legal narrow transfers, two per 16-byte line) returns wrong
data when the beats are back to back:

| host beats | family | result (1:4 proxy, 2026-10-29) |
|---|---|---|
| 16-byte (full width) | incremental / row_major / col_ilv / col_major | 0 mismatched, 1135/1151, 1148/1148, 918/913, 666/713 MB/s of 1200 |
| 8-byte (narrow) | incremental | **1020 of 1024 beats wrong**, 568/575 MB/s |
| 8-byte (narrow) | col_major | 0 mismatched (page misses space the reads) |
| 4-byte (narrow) on the 64-bit 1:2 host | incremental / col_major | 0 mismatched |

Each narrow beat becomes its own BL8 read of the same 16-byte line (the
aligner probe counts one RD command and one valid per beat: 2048 for
1024 lines, nothing duplicated at the PHY), so the defect is in how the
read return path serves two same-line, adjacent reads to half-width
beats, not in the DFI plane. The 1:2 64-bit host with 4-byte beats (two
per 8-byte word) is clean, so it is specific to the 1:4 geometry
(BURST_WORDS 1, AXI_BEATS_PER_BURST 1) or to adjacent same-column reads.

On the board (1:4 ILA bitstream, 2026-10-29) the same narrow read gives
the same one-wrong-word-per-run as the full-width read (TASK-003 item 6),
and a **narrow write started after that mismatching read hangs the write
engine** until a soft reset (seen twice; full-width writes after a
mismatching read hang the same way -- so this half is likely the
harness's latched rd_error / engine state, not the controller; separate
it first).

## Repro

```
cd projects/fpga-systems/NexysA7/mem-ctrl-ip-ddr2/ddr2_char_framework/dv/tests
TEST_AXI_SIZE=3 TEST_AXI_DATA_WIDTH=128 TEST_DFI_RATE=4 TEST_DRAM_BL=8 \
TEST_DRAM_BEAT_BYTES=4 TEST_DRAM_DEVICE_BYTES=2 TEST_T_RDDATA_EN=1 \
TEST_FAMILIES=incremental PERF_ALWAYS_DIAG=1 pytest -q test_granite_char_perf.py
```
(`TEST_AXI_SIZE` forces the beat size; without it the proxy now drives
full-width beats at `TEST_AXI_DATA_WIDTH`.)

## Done when

Narrow beats at every legal AxSIZE on the 128-bit host return the right
data back to back (a directed core TB case per AxSIZE, and the proxy
line above clean), and the post-mismatch write hang is attributed.

## Resolution (2026-11-02)

**Root cause: the controller had no narrow-burst support at all.** It is not
the return path. `mc_axi_burst_chopper` steps every sub-command by
`AXI_BEATS_PER_BURST` full beats, and the intakes count one AXI beat as one
data word, whatever AxSIZE says. On a host as wide as the controller (the 1:4
build's 128-bit core), a narrow INCR burst therefore wrote and read a
different word on every beat after the first. The 1:2 64-bit host was clean
because that controller is 32 bits wide, so a 4-byte beat is full width
there. `mc_axi4_half_agg`'s header already said so ("the controller's chopper
has no narrow-burst support"). Repro on HEAD unchanged from 10-29: 1020
mismatched.

**Fix: `common-ip/rtl/fub/mc_axi4_narrow_pack.sv`**, in `mc_axi4_plane` between
the host edge and the splitters (`NARROW_EN`, default 1; `NARROW_DEPTH` =
`RD_RET_DEPTH + 8`). A narrow INCR burst is rewritten to the full-width INCR
burst over the same words (address aligned to the word, AxLEN = words spanned
- 1, counted from the first beat's size-aligned offset). W beats are packed
into their word by strobe, and each R word is presented once per narrow beat
in it. Full-width bursts and narrow FIXED / WRAP pass through
combinationally; the controller supports FIXED and WRAP at no width. W never
waits on the controller's AW handshake. AWs are accepted upstream into an
`NARROW_AWQ_DEPTH` (8) queue when the controller back-pressures AW, with a
same-cycle bypass when it does not, so W runs ahead exactly as before and
the controller-side AW stream is unchanged. The first version gated W on the
controller's AW handshake. pumice's board-geometry `perf_write_ceiling`
caught it (17 W stall cycles against a budget of 16, HEAD 2), and so did
`perf_paging_sched_cross` (pref_row_first 28.74 against a 30 percent floor).
Both pass with the queue. The plane is shared, so pumice, scoria and andesite get the
fix too.

**Evidence**
- 1:4 proxy, 128-bit host, incremental, 8-byte beats: 1020 -> **0**
  mismatched, wr / rd 567.5 / 577.6 -> 585.6 / 592.6 MB/s (host cap 600). One
  burst now carries two narrow beats instead of costing one BL8 each.
- Every narrow AxSIZE on that host, incremental and col_major: 0 mismatched
  at the host-beat ceiling (1 B 74.2 / 74.1, 2 B 148.4 / 148.2,
  4 B 297.3 / 296.3 MB/s of 75 / 150 / 300).
- `test_granite_core.py::test_granite_core_narrow[0..4]`: one DRAM burst
  written and read as narrow beats at each AxSIZE; the DFI write bus must
  carry exactly the packed BL_WORDS words. With `NARROW_EN=0` cells 0..3 fail
  (64 / 32 / 16 / 8 DFI words for one burst) and 4 passes.
- `common-ip/dv/tests/fub/test_mc_axi4_narrow_pack.py`: AXI4 master BFM to
  AXI4 slave BFM with a byte memory, every AxSIZE, unaligned starts, FIXED /
  WRAP, multi-ID concurrent reads, both timing profiles, 32- and 128-bit; the
  command rewrite is checked independently. Mutations caught: no rewrite
  (narrow INCR reaches the controller), no W accumulator (1752 bad bytes),
  no R replay (timeout), word count ignoring the first beat's offset
  (timeout), AW queue disabled (timeout); under randomized timing 232 to 280
  W beats per cell run ahead of a queued AW.

**The post-mismatch write hang is the harness, not the controller.** Sim on
the pre-fix tree, families incremental then row_major, no soft reset between
them: the row_major write after the mismatching read completes (2163 cycles,
wr_ok). `granite_char_harness.sv` drives `w_wr_error = w_gen_any_error`, which
includes read data errors, into a sticky latch, and the host's
`ddr2_char.wait_done()` raises on `STATUS.any_error`. So after any
mismatching read, every later run reports an error at its first poll until a
soft reset (or `clear_stats`) clears it. The same aliasing is in
`ddr2_char_harness.sv`. That is a harness reporting choice, left as it is;
the TASK-009 first-word defect is what produced the board's mismatching read.

**Cost and regressions (final RTL)**
- 1:4 proxy, full-width beats, same seeds, HEAD against fix: incremental,
  row_major and col_ilv are cycle-identical both ways, and col_major writes
  match (3710 cycles). col_major reads were 3176 -> 3207 in the four-family
  sequence. col_major run alone gives 3207 on HEAD, on the fix and on the fix
  with a 128-deep record queue, so the block is not the cost; the difference
  is the state carried in from the preceding families (the refresh-phase
  sensitivity in TASK-003's log).
- granite 100 MHz board build (GRANITE_SYS_100, ExtraNetDelay_high, single
  pass, fresh trees): HEAD WNS -0.037 ns (4 of 109,520); fix **+0.001 ns, 0
  failing**. That is placement noise on a knife-edge design, not a gain; the
  block adds no timing problem. `u_narrow` routed: 331 LUT (96 LUTRAM), 135 FF.
- Regressions, clean-all, func: granite 27 passed / 1 xfail (22 + the 5 narrow
  cells); pumice 222/222 at both geometries; common-ip fub 47/47. scoria (12)
  and andesite (21) fail the same set at HEAD and with the fix: pre-existing,
  in `mc_bank_timer` gaps one cycle short, the scheduler planes and
  andesite's core TB (`t_rfc_wait_i` is not a port). Not this change.

**CLOSED 2026-11-02.**
