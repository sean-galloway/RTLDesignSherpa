# TASK-002: pipelined cycle injector -- measure hit throughput and memory-level parallelism, not just latency

**Date:** 2026-11-11
**Priority:** P1
**Status:** CLOSED 2026-11-11 (commit 561a3e747) -- both rigs rebuilt and swept at depths 1, 2, 4, 8, 16; jet BUG-004 found and fixed on the way.
**Owner:** cache-ip

## Why

The Genesys2 pair rigs drive both caches from `amber_cycle_injector`, a
blocking stimulus engine: one request outstanding, `FSM_ADDR_WAIT ->
FSM_ISSUE -> FSM_WAIT_RSP` per transaction. Every number in the J7 report
and the FPGA-review sweeps is therefore latency-bound: 20k all-hit
transactions take ~100k cycles on a 3-cycle jet because the injector adds
two cycles of its own and never has a second request in flight. We measure
hit latency well and hit throughput, sustained MLP and the effect of the
response ring depth not at all -- which is exactly what a comparison against
a non-blocking reference cache (TASK-003) needs. Owner, 2026-11-11: "The
injector MUST be pipelined."

## What

1. `amber_cycle_injector` becomes a credit-based pipelined master: the
   house `dma_address_gen` runs full (its 2-stage pipe, LFSR as the
   pass-through tag so address / we / be / wdata stay one LFSR step per
   transaction), issue is gated at the `cpu_req` port by an outstanding
   credit `CTRL[23:16]` (0 = 1, back-compatible), responses are taken
   whenever offered, and per-request latency comes from an accept-timestamp
   ring popped in response order (both caches return CPU responses in
   accept order: amber is blocking, `jet_rsp_seq` is the ordering point).
2. New read-only counters in the free top of the 32-word window:
   `OUTST_MAX`, `OUTST_SUM_LO/HI` (mean achieved outstanding = MLP),
   `STALL_CYCLES` (cycles the cache held `cpu_req_wr_ready` low against a
   valid request). Existing CSRs keep their offsets and meaning.
3. Host: `CycleInjector.configure(outstanding=...)`, `latency()` returns the
   new counters, perf sweeps take `--outstanding` (list) and record it per
   result, printing cycles/txn and MLP. Both rigs (amber, jet).
4. Harness AXIL tests: a pipelined-run test on both rigs -- depth 1 and
   depth 8 give identical CRCs (the issued sequence is depth-invariant),
   identical lat_min, fewer run cycles, sane counters.

## Done when

- Both harness gates green (amber-g2, jet-g2); injector lint clean.
- The stimulus is unchanged and depth-invariant: per-config `wdata_crc`
  identical to bin 16 (jet) / bin 9 (amber) at every depth, and `rsp_crc`
  identical wherever the read data cannot depend on the two injectors'
  interleaving (ci1 in disjoint64k, whose 0x40000 region no other config
  touches). As first written this bullet demanded every `rsp_crc` match;
  that was over-specified -- a shared-region read returns whichever
  injector's write landed last, so its CRC encodes the race, and the
  pipelined injector's depth-1 turnaround is already a cycle shorter than
  the blocking FSM's (5.05 -> 4.08 cycles per hit), which moves the race.
- Genesys2 builds for both rigs: WNS >= 0 under the 0.200 ns budget,
  smoke PASS, sweep err 0 at depths 1, 2, 4, 8, 16; results JSON per depth.
- Hit throughput and MLP tables for amber and jet in this task's closure
  and the J7 report.

## Progress

### 2026-11-11 -- the pipelined injector found a jet deadlock

Amber-g2 gate green (2/2, 158 s). Jet-g2 gate: `injector_pipeline_test`
hung at depth 8 (depth 1 passed, 256/256, hit floor 3). Both caches parked
with an AR held by the fabric, a launch pending in the fill-launch register
and a further miss at the lookup; the fabric sat in F_AC because its
safe-peer wait demanded an idle peer lookup -- which a pipelined stream never
grants while the peer's own fill waits on that same fabric. Filed and fixed
as jet BUG-004 (`jet_pair_fabric.sv` pending bypass; pair-rig scenario (i)
pins it at every level; jet rig lint clean). Blocking injectors and the
rig's 1..3-deep random bursts could never produce the posture: this is the
first result of the pipelined injector, before any number was measured.
Clean jet FULL, jet-g2 gate and the bin 11 / bin 17 board flow re-queued.

### 2026-11-11 CLOSED -- both rigs rebuilt and swept at depths 1, 2, 4, 8, 16

Gates: amber-g2 2/2 (149 s), jet-g2 2/2 (175 s) from clean, with
`injector_pipeline_test` at depths 1 / 8 / 255 (clamped to 16) on both;
clean jet FULL 149/149 including the new pair-rig scenario (i); injector
and jet rig lint clean.

Boards (one flow at a time under `board_lock.sh`; program, smoke, sweep):

| rig | bin | LUT | FF | WNS (0.2 ns clock-uncertainty budget) | smoke | sweep err |
|---|---|---|---|---|---|---|
| amber | 11 | 17,794 (+609 vs TASK-001's 17,185) | 20,013 | +0.369 | PASS | 0 at every depth |
| jet | 17 | 22,524 (+810 vs bin 16) | 24,760 (+492) | +0.212 | PASS | 0 at every depth |

The growth is the two injectors: 16 x 32-bit timestamp ring, 16-entry
credit/inflight bookkeeping, four counters each.

**amber (bin11, `perf_sweep_bin11_20261111T212718Z.json`)** -- cycles per transaction (ci0) and mean MLP (ci0) per depth; 20,000 transactions per run, both injectors on the same region except disjoint64k:

| config | d1 cyc/txn | d2 cyc/txn | d4 cyc/txn | d8 cyc/txn | d16 cyc/txn | d1 MLP | d2 MLP | d4 MLP | d8 MLP | d16 MLP | OUTST_MAX d16 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| smoke4k_we64 | 5.08 | 3.04 | 3.04 | 3.04 | 3.04 | 0.80 | 1.33 | 1.33 | 1.33 | 1.33 | 2/2 |
| r4k_we0 | 5.02 | 3.04 | 3.04 | 3.04 | 3.04 | 0.80 | 1.33 | 1.33 | 1.33 | 1.33 | 2/2 |
| r4k_we255 | 5.04 | 3.04 | 3.04 | 3.04 | 3.04 | 0.80 | 1.33 | 1.33 | 1.33 | 1.33 | 2/2 |
| r1k_we64 | 5.02 | 3.03 | 3.03 | 3.03 | 3.03 | 0.80 | 1.33 | 1.33 | 1.33 | 1.33 | 2/2 |
| r64b_we64 | 5.00 | 3.00 | 3.00 | 3.00 | 3.00 | 0.80 | 1.33 | 1.33 | 1.33 | 1.33 | 2/2 |
| r16k_we64 | 5.32 | 3.27 | 3.27 | 3.27 | 3.27 | 0.81 | 1.31 | 1.31 | 1.31 | 1.31 | 2/2 |
| r64k_we64 | 20.83 | 18.82 | 18.82 | 18.82 | 18.82 | 0.95 | 1.05 | 1.05 | 1.05 | 1.05 | 2/2 |
| r64k_we255 | 30.49 | 28.49 | 28.49 | 28.49 | 28.49 | 0.97 | 1.04 | 1.04 | 1.04 | 1.04 | 2/2 |
| r128k_we64 | 28.62 | 26.62 | 26.62 | 26.62 | 26.62 | 0.97 | 1.04 | 1.04 | 1.04 | 1.04 | 2/2 |
| disjoint64k_we64 | 20.86 | 18.86 | 18.86 | 18.86 | 18.86 | 0.95 | 1.05 | 1.05 | 1.05 | 1.05 | 2/2 |
| smoke4k_we64_repeat | 5.06 | 3.06 | 3.06 | 3.06 | 3.06 | 0.80 | 1.33 | 1.33 | 1.33 | 1.33 | 2/2 |

**jet (bin17, `perf_sweep_bin17_20261111T213557Z.json`)** -- cycles per transaction (ci0) and mean MLP (ci0) per depth; 20,000 transactions per run, both injectors on the same region except disjoint64k:

| config | d1 cyc/txn | d2 cyc/txn | d4 cyc/txn | d8 cyc/txn | d16 cyc/txn | d1 MLP | d2 MLP | d4 MLP | d8 MLP | d16 MLP | OUTST_MAX d16 |
|---|---|---|---|---|---|---|---|---|---|---|---|
| smoke4k_we64 | 4.08 | 2.03 | 1.03 | 1.03 | 1.03 | 0.75 | 1.51 | 3.03 | 4.29 | 4.66 | 12/12 |
| r4k_we0 | 4.02 | 2.03 | 1.03 | 1.02 | 1.02 | 0.75 | 1.51 | 3.03 | 7.02 | 11.00 | 12/3 |
| r4k_we255 | 4.04 | 2.04 | 1.06 | 1.06 | 1.06 | 0.75 | 1.51 | 3.06 | 4.10 | 4.21 | 12/12 |
| r1k_we64 | 4.02 | 2.02 | 1.05 | 1.05 | 1.05 | 0.75 | 1.51 | 3.05 | 4.04 | 4.07 | 12/12 |
| r64b_we64 | 4.00 | 2.00 | 1.25 | 1.25 | 1.25 | 0.75 | 1.50 | 3.20 | 3.80 | 3.80 | 4/11 |
| r16k_we64 | 4.31 | 2.21 | 1.21 | 1.19 | 1.18 | 0.77 | 1.55 | 3.17 | 4.88 | 5.66 | 12/12 |
| r64k_we64 | 17.43 | 12.93 | 11.48 | 10.82 | 10.74 | 0.94 | 1.92 | 3.91 | 6.43 | 7.04 | 12/12 |
| r64k_we255 | 21.18 | 14.32 | 12.10 | 11.04 | 10.90 | 0.95 | 1.93 | 3.92 | 6.38 | 6.97 | 12/12 |
| r128k_we64 | 24.01 | 17.30 | 16.34 | 16.04 | 16.02 | 0.96 | 1.94 | 3.94 | 5.69 | 5.82 | 12/12 |
| disjoint64k_we64 | 17.46 | 12.98 | 11.53 | 10.88 | 10.80 | 0.94 | 1.92 | 3.91 | 6.41 | 7.02 | 12/12 |
| smoke4k_we64_repeat | 4.05 | 2.04 | 1.05 | 1.04 | 1.04 | 0.75 | 1.51 | 3.05 | 4.30 | 4.65 | 12/12 |

Reading the tables:

- **amber** is blocking at its CPU port with a one-deep request skid: the
  second credit is accepted into the skid and hides the injector's own
  turnaround (5.0 -> 3.0 cycles per resident hit), and nothing beyond two
  is ever in flight (OUTST_MAX 2 at every depth >= 2). Its MLP ceiling is
  1.33 on hits and 1.05 on misses. That is the design: amber's number is
  the blocking baseline the J7 comparison needs.
- **jet** sustains one resident hit per cycle from depth 4 (1.03 cycles
  per transaction, MLP 3-4.7 on the 1-4 KB working sets) and overlaps
  misses up to MLP 7.0 with 12 in flight (OUTST_MAX 12 = the response ring
  plus the lookup pipe): the 64 KB thrash goes 17.4 -> 10.7 cycles per
  transaction (-38 %), 128 KB 24.0 -> 16.0 (-33 %). The miss-side curve is
  nearly flat from depth 8 to 16, so the memory path (one AR in flight at
  the pair fabric) is the next limiter, not the cache.
- Mean hit latency rises with depth (jet smoke4k 3.08 -> 4.79) because a
  queued hit waits behind the one ahead of it; the *floor* stays 3 except
  where no hit ever found the pipe idle (ci1 at depth 16 reports 4).
- Observation, not chased: on jet's read-only 4 KB config (`r4k_we0`) the
  two injectors are asymmetric at depth >= 8 -- ci0 piles up to 12 in
  flight (mean latency 11.2 at 1.02 cycles per transaction) while ci1
  never exceeds 3 (latency exactly 3.00 at 1.00 cycles per transaction).
  Both run at full throughput; only the intake depth differs. Deterministic
  across depths 8 and 16. Worth a look when the J7 fairness question is
  taken up; no error flag, no CRC effect.

CRCs (`wdata_crc` and `rsp_crc` per config per depth, both rigs, 110 pairs
each): every `wdata_crc` equals the bin 16 / bin 9 baseline; `rsp_crc`
equals the baseline for ci1 in disjoint64k at every depth (its region is
private to the config), and differs for shared-region reads as the revised
bullet above explains. Within a sweep, ci1's disjoint `rsp_crc` is the
same at depths 1 through 16: the issued stream is depth-invariant on the
board as it is in simulation. Depth 1 reproduces the blocking injector's
accounting (OUTST_MAX 1, hit floor 3 on jet / 4 on amber).

Found on the way: jet BUG-004 (closed with this task) -- the pair fabric's
safe-peer wait deadlocked under the first pipelined stream; fixed in the
fabric, pinned by pair-rig scenario (i), lesson added to the handbook
note `design/holds-that-wait-on-the-fabric.md`.

J7 report: section "Pipelined injector" added with the jet table and the
amber comparison. TASK-003 (reference caches) starts next on this injector.
