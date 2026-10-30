---
title: TASK-005 — the simple AXI aggregator in granite's AXI plane, for the half-burst pair walk
summary: Drop the amba axi4_aggregator_cmd pairing core into mc_axi4_plane behind a parameter (granite on, pumice off) with a narrow-to-full W packer and R replay, so two adjacent half-width single beats cost one DRAM burst; measure on the board; defer if it is more trouble than the one cell it buys.
---

# TASK-005 — the simple AXI aggregator in granite's AXI plane, for the half-burst pair walk

**State:** deferred · **Area:** product-ip/granite-ddr2-lpddr2 · **Opened:** 2026-10-29
**Status:** deferred 2026-10-29 -- measured, more problem than it is worth (owner's
rule); un-deferred by a master whose traffic is adjacent same-ID half-width
pairs AND is DRAM-bound rather than issue-rate-bound, or by a fix of the
open_page write hang if the block is ever wanted on. The block stays in the
tree behind `HALF_AGG = 0` (granite_core, geared top, plane), lint-clean,
with the on state runnable (`GRANITE_HALF_AGG=1`).
**Owner's direction (2026-10-29):** "can you try dropping in the aggregator
into either the axi-plane, or the storage-plane? Please file this and we
will defer if it is more problem than it is worth."
**Parent:** TASK-003 (the half-burst pair walk at one thread is the one
cell where LiteDRAM leads at 75 MHz: 286 vs 240 rd MB/s).

## Why

The half-burst families (pumice TASK-060) issue single-beat half-width
commands to the two halves of one DRAM burst. Granite's splitter pads every
short beat to a whole DRAM burst with the data mask, so each half costs a
full burst and the pair walk reads exactly half the stream rate (288 / 240
vs 576 / 578 at 75 MHz). The amba aggregators (`rtl/amba/shared/
axi4_aggregator_cmd.sv` and its wr / rd wrappers, 2026-10-28) pair lo and
hi into one 2-beat command with a held command, a hold counter and side
FIFOs, no CAM. Pumice's CAM combiner shows the ceiling for this traffic:
every pair merges through three threads and the oct walk never merges even
with the CAM, so the simple rule gives up nothing here.

## Why not just the wrappers

The wrappers emit the pair as a 2-beat burst at the narrow size and pass W
and R through. Granite's chopper counts AXI beats regardless of size and
steps sub-command addresses by the full DRAM burst
(`mc_axi_burst_chopper.sv:183`), so a 2-beat narrow burst would become two
sub-commands with the hi half at lo + 8. The plane needs the pairing core
plus: the merged command rewritten to one full-width beat (len 0, size
full), a W packer that folds the two narrow beats into one by strobe, a B
replay (one B presented twice) and an R replay (the one full beat presented
twice with RLAST, since each half's lanes are in the same word).

## Plan

1. `mc_axi4_half_agg` (common-ip fub): the pairing core on AW and AR at
   DATA_WIDTH = DW / 2, side queues for W, B and R, the packer and the two
   replays. Parameter `HALF_AGG` on `mc_axi4_plane`, default 0 (pumice
   untouched, generate bypass); `granite_core` passes 1; the granite top
   tests take `GRANITE_HALF_AGG` so the off state runs.
2. Gates: lint; granite top func on and off; common-ip fub + macro; pumice
   top (218); perf proxy cycle-identical on the full-width families (they
   never pair).
3. Board, 75 MHz: `half_threads` against `char_granite_setlag75_half_threads_2026-10-29.csv`
   (expect the pair walk at one thread to reach the stream rate; the oct
   walk unchanged) and the four other profiles against the same day's CSVs
   (expect unchanged). Then the DDR2-400 point.

## Acceptance / defer rule

Keep it if the pair walk at one thread moves to the stream rate with every
other cell unchanged and zero mismatches, and the LUT cost stays in the low
hundreds. Defer (owner's word) if it costs timing at 100 MHz, perturbs the
full-width cells, or needs changes below the plane.

## Results log

(filled as it lands)

### 2026-10-29, pass 1: the block, the gates, and a side-queue lesson

`mc_axi4_half_agg` written (common-ip fub, 330 lines: two `axi4_aggregator_cmd`
cores at DW/2, three one-bit side queues, the W packer, the B and R
replays), `HALF_AGG` on `mc_axi4_plane` (default 0), granite_core and the
geared top pass 1, the granite top tests take `GRANITE_HALF_AGG`. Lint
clean on granite at both settings and on pumice_core. Gates on the text:
granite_core func on and off (2 / 2), granite top func 6 passed 1 xfail,
common-ip 34 passed 3 xfail on a clean build (a first run reported the
same in 1.8 s: the suite's build dirs are `fub/local_sim_build` and
`macro/local_sim_build`, and a `rm` one level up removes nothing), pumice
top 218 passed with the parameter off. The harness injectors drive
AxCACHE 0011, so their commands are modifiable and pair.

**Side-queue depth is the plane's outstanding capacity, not a small
constant.** The first text took the amba wrappers' `AGG_FIFO_DEPTH = 4`.
An AW or AR issues only when its side queue can record it, and the entry
is popped at the B or the R, so the depth caps the commands in flight per
direction. The perf proxy saw it on full-width traffic that never pairs
(incremental rd 2157 -> 2165 cycles, col_ilv rd 2717 -> 2711); the board
saw it in full. 75 MHz build at depth 4: WNS +0.935, 0 failing, 37,086
LUTs (+700 over the 36,386 baseline). Board, zero mismatches in every
cell, bandwidth throttled everywhere reads are deep:

| 75 MHz, open_page, MB/s wr / rd | baseline (setlag75) | HALF_AGG, depth 4 |
|---|---|---|
| half pair walk, 1 / 2 / 4 threads | 288/240, 287/288, 214/249 | 74/36, 66/34, 72/35 |
| streams incremental / row_major | 576/578, 578/580 | 576/465, 578/466 |
| 1w+1r incremental / row_major, per direction | 284/284, 288/288 | 252/252, 254/254 |
| 1w+2r row_major | 170/340 | 158/317 |

Four single-beat reads over a ~50-cycle latency is about 48 MB/s, which is
the half-burst read column. Fixed: `HALF_AGG_DEPTH = RD_RET_DEPTH` (32),
after which the proxy is cycle-identical on all four full-width families
(2164/2157, 2154/2141, 2672/2717, 3972/3464, seed 2882343476). Depth-32
build and board run queued; CSVs of the depth-4 run kept as
`char_granite_halfagg75_*_2026-10-29.csv` for the record.

Side observation for pumice ISSUE-025: with only four reads in flight the
histogram 1:1 note vanished on every `half_threads` cell (32 of 32 ok),
so the under-count is an outstanding-depth effect in the harness's
latency histogram, not a per-thread one.

### 2026-10-29, pass 2: depth 32, the ID rule, and the verdict

Depth-32 build: WNS +0.894, 0 failing, 37,110 LUTs (+724 over the 36,386
baseline; the block is the two cores, three 32-deep one-bit queues and the
64-bit W packer). Board, zero mismatches in every cell of every profile:

| 75 MHz open_page, MB/s wr / rd | baseline | HALF_AGG depth 32, counter IDs | HALF_AGG depth 32, fixed ID |
|---|---|---|---|
| pair walk, 1 thread | 288/240 | 196/196 | **write engine hung** / 237 |
| pair walk, 2 / 3 / 4 threads | 287/288, 257/281, 214/249 | 195/195, 194/194, 192/189 | 195/194 (flagged), 194/194, 192/189 |
| oct walk, 1 / 4 threads | 288/240, 214/249 | 197/196, 178/180 | 197/196, 178/180 |
| close_page pair walk, 1 thread | 30/37 | 30/37 | **60/75** |
| close_page pair walk, 2 / 3 / 4 threads | 49/59, 73/87, 96/96 | unchanged | unchanged |
| streams, 1w+1r, 1w+2r (all four families) | as 2026-10-29 | identical (0.1 MB/s) | not rerun |

CSVs `char_granite_halfagg75d32_*_2026-10-29.csv`,
`char_granite_halfagg75d32_fixedid_half_threads_2026-10-29.csv`, and the
like-for-like baseline `char_granite_setlag75_fixedid_half_threads_2026-10-29.csv`
(`HALF_ID_FIXED=1` on `half_burst_family.programs`, a switch added for this).

What the table says, in order:

1. **The profile's counter IDs defeat the rule.** The pairing core requires
   the same ID, and `half_threads` gives every transaction the next ID, so
   nothing paired on the first run and the close_page cells are identical
   to the byte. With one ID per thread the close_page one-thread cell
   doubles (30/37 to 60/75): the block pairs and the packer / replays are
   right for that case.
2. **The open_page pair cell cannot gain.** At one thread the baseline's
   240 MB/s of half-width reads is one command per 2.5 cycles from the
   injector, not a DRAM limit; merging halves the DRAM work and the host
   issue rate stays the bottleneck (237 vs 239). The cell where LiteDRAM
   leads is host-bound in this harness, so no controller-side pairing
   moves it.
3. **Every unpaired half-width command pays the hold.** A lone lo waits
   HOLD_CYCLES + 1 before leaving, and at two or more threads the port mux
   breaks adjacency so every lo is lone: 30 percent off writes and 18 off
   reads on the pair and oct walks, at every thread count.
4. **A write hang.** open_page one-thread pair walk with fixed IDs: "write
   engine did not complete" (read pass fine, 237). The W packer holds W
   until its AW has issued and the pairing core holds the AW for its
   partner; some interleaving of the injector's AW and W against that pair
   of holds stops the write pass. Not diagnosed: the verdict does not
   depend on it, and the block is off.

Full-width traffic is untouched at depth 32 (every stream, 1w+1r and 1w+2r
cell within 0.1 MB/s of the baseline; proxy cycle-identical), and the 100
MHz close is not re-measured (the block is off in the shipped text).

Verdict (owner's rule, 2026-10-29): defer. Keep the block in the tree, off.
If it is ever wanted, it belongs per master port ahead of the interconnect
where adjacency holds, with a cross-ID pairing variant (the replays would
carry the second ID) and the W hold resolved; and the win exists only for a
DRAM-bound master, which the char injectors are not.
