# ISSUE-003: two jet cores sharing nothing lose every pipelining gain -- the dual run is flat at ~480,000 cycles from depth 1 to 16

**Status:** closed 2026-11-27 -- explained: a structural limit of jet's serial
pair fabric, by design; no jet RTL change (jet is the frozen baseline;
jet-prime's slotted fabric and onyx are the design that removes it).
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

## Resolution (2026-11-27): traced in the harness sim

The jet harness sim reproduces the board cells from reset within 1 %
(`smoke_test`, `JET_SMOKE_MASK=0xFFFF JET_SMOKE_BASE1=0x40000
JET_SMOKE_WE_MIX=64 JET_SMOKE_COUNT=20000`, `JET_SMOKE_GO=0x1` for the
single run), with `JET_FABRIC_PROBE=<json>` counting the fabric's
coherence-FSM cycles per state and, while it waits on the peer's CR, the
peer control's snoop-safe terms:

| run | sim cycles (board) | misses | fabric busy | per miss: AC + AR + DONE / snoop answer / memory read |
|---|---|---|---|---|
| single d1 | 350,388 (349,394) | 10,279 | 50 % | 3 / 3.0 / 11.0 |
| single d16 | 216,835 (215,038) | 10,279 | 81 % | 3 / 3.0 / 11.0 |
| dual d1 | 484,003 (481,080) | 20,443 | 90 % | 3 / 7.4 / 11.0 |
| dual d16 | 492,689 (491,961) | 20,443 | 96 % | 3 / 9.1 / 11.0 |

Two causes, both structural:

1. **The fabric runs one coherence transaction at a time** (its header:
   "ONE coherence transaction at a time"), 17 cycles a miss from grant to
   the last R beat when the peer answers at once. One core at depth 16
   already keeps it 81 % busy; two cores need twice the fabric time,
   20,443 x 17 = 347.5k cycles -- a floor above the single core's 215k at
   any depth.
2. **Every snoop lands in the peer's commit window.** The fabric's
   round-robin alternates the caches, so right after it completes cache A's
   fill it grants B and snoops A, whose just-filled line is committing.
   jet_control holds the answer while `sn_safe_o` is low (`w_any_done`: a
   fill done, not retired; `w_cap_active`: a dirty victim's capture). At
   dual depth 16, of the 9.1 cycles a miss waits for the CR, 3.0 are the
   single run's own request-and-grant cycles and 6.1 the peer's windows
   (commit 4.1, capture 1.1, both 0.9); single core: 0. Together: 347.5k +
   124.3k = 471.8k against 471.9k fabric-busy cycles measured, in a 492.7k
   run.

Depth does not help the dual run because the fabric, not the core, is the
bottleneck from depth 1 on (90 % busy). jet-prime's `jet_prime_pair_fabric`
and onyx hold several transactions in a table and overlap the memory read
with the snoop, which is why they cost 1.4-1.7x single-core here. Not a
bug: the serial fabric is jet's documented design, and changing it is
exactly the jet-prime fork's purpose.
