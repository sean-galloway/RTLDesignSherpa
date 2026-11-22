# ISSUE-001: the board MonBus channel cannot carry onyx's event stream; tally bins are lower bounds

**Priority:** P3
**Status:** open
**Owner:** TBD
**Filed:** 2026-11-22 (onyx TASK-001 step 6b)

## Observed

On the Genesys2 reference rig (`REF_CACHE_SEL` 4 and 5, bin 2 builds with the
pair block's MonBus tally chain), the `monbus_tally_axil` bins for onyx's
event classes fall far short of the exact counters in every cell with a
sustained event rate, while the resident and warm-up cells agree exactly:

| cell (dual sweep) | transactions (counter) | `TXN_START` (bin 11) | `MEM_READ` counter / bin | drop-report packets (bin 17) |
|---|---|---|---|---|
| `r4k_we0` depth 1 | 16 | 16 | 16 / 16 | 0 |
| `r16k_we64` depth 1 | 381 | 265 | 381 / 266 | 2 |
| `r64k_we64` depth 1 | 20,240 | 12,613 | 20,240 / 12,603 | 2 |
| `r64k_we64` depth 16 | 20,240 | 3,891 | 20,239 / 3,888 | 2 |
| `r128k_we64` depth 16 | 30,083 | 5,360 | 30,072 / 5,359 | 2 |

Results: `perf_sweep_onyx_bin2_dual_20261122T151054Z.json` and the three
companions (`ref/results/`). In simulation the same observer loses 0 to 9
events per full-regression cell and reports every one (the pair-rig TB
holds it to that); on the board the observer's holders overflow for the
whole run.

## Why

The pair block's one MonBus channel (`monbus_arbiter`, 3 clients ->
`monbus_axil4_group_1wr` -> `monbus_tally_axil`) is bounded by the group
writer: one AXI-Lite write transaction per packet word, several cycles a
packet, shared by the two caches' observers and onyx's. Delivered rate on
`r64k_we64` depth 1 is about 0.17 onyx packets a cycle plus a similar cache
stream; onyx alone generates about four events per transaction at a
transaction every three cycles per injector. The drop-and-count idiom
(inherited from the caches' observers) reports the loss poorly under
sustained load: the report is emitted only when nothing is waiting, and its
payload is 8 bits, so two reports a cell stand for thousands of lost events.

## What is not affected

The six exact counters (`onyx_counters`, harness CSR 0x020-0x034) are the
D6 measurement and are unaffected: they agree with the pair-rig model in
sim and with each other on the board (reads wasted == lines supplied in
parallel mode; memory reads fall by exactly lines supplied in deferred
mode; zero wasted). All 220 bin 2 cells reproduce their bin 1 cycle counts,
so the chain costs no cycle.

## Resolves into

One of: (a) record as a known limit of the house chain on this rig (the
tally bins are lower bounds; the counters are the instrument), with the
HAS and comparison saying so (done in ch04/04 and ch06/02); (b) a task to
raise the channel's rate (compression on the group writer, or a tally fed
directly from the arbiter without the AXI-Lite hop); (c) a task on the
drop-and-count idiom itself (a wider saturating payload, or a periodic
report), which the caches' observers would share. (b) and (c) are
observation plumbing, not onyx, and belong with the monitor area if taken.
