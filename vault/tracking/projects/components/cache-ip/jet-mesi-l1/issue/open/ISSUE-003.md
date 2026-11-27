# ISSUE-003: two jet cores sharing nothing lose every pipelining gain -- the dual run is flat at ~480,000 cycles from depth 1 to 16

**Status:** open (filed 2026-11-27).
**Owner:** TBD
**Where:** suspected `rtl/top/jet_pair_fabric.sv` (one coherent
transaction at a time); not traced.

## What was seen

Board bin 21 (the jet BUG-008 fix; `jet/results/perf_sweep_bin21_bug008{,_single}_20261127T174527Z.json`),
20,000 transactions a side, 0 errors:

| config | depth | dual ci0 / ci1 | single (ci1 idle) |
|---|---|---|---|
| `disjoint64k_we64` (no shared line: base1 0x40000) | 1 | 481,080 / 480,704 | 349,394 |
| | 2 | 468,799 / 468,650 | 259,126 |
| | 4 | 482,854 / 482,294 | 229,918 |
| | 16 | 491,961 / 491,361 | 215,038 |
| `r64k_we64` (shared) | 1 | 528,377 / 524,771 | 347,218 |
| | 16 | 531,298 / 528,535 | 212,971 |

Single-core the injector's depth buys 1.6x (349k -> 215k); with the peer
running on disjoint lines it buys nothing. jet-prime's pipelined pair
fabric and onyx on the same configs cost 1.4-1.7x single-core at depth
>= 4 (`reference_l1_comparison.md`, two-core table); jet costs 2.1-2.3x.
BUG-008's fix left this unchanged (bin 20 2.10x / 2.30x, bin 21 2.10x /
2.29x), so it is not that wait.

## Open question

Where the dual run's cycles go. The hypothesis to test first: every jet
miss is a coherent transaction through `jet_pair_fabric`, which runs one
at a time (grant -> snoop -> response -> memory), so two caches' misses
serialize at the fabric even when they share no line, and the second
core's misses fill the gaps the first core's pipelining left. If so it
is a known structural limit of the serial fabric (jet-prime's fabric has
slots), and this resolves to a recorded no-action or a task; if not, to
a bug.

## How to look

The jet harness sim reproduces board cells from reset (`smoke_test`
with `JET_SMOKE_MASK=0xFFFF JET_SMOKE_BASE1=0x40000 JET_SMOKE_WE_MIX=64
JET_SMOKE_OUTSTANDING=4`): measure the fabric's busy cycles (state_q !=
F_IDLE) against the run, and the per-cache wait from AR valid to grant.
