# TASK-004: CPU-side clean-all request for peregrine's fence.i

**Priority:** P3
**Status:** closed (2026-11-24): clean-all landed (da9e8df71); peregrine `fence_i` and `Zifencei` pass at `CACHE_EN=1`
**Owner:** TBD (filed from riscv-ip/peregrine-rv32im PRD 0.2 P10, ruled
2026-11-23 by the owner: "accept defaults on the rest")

## Why

peregrine (amber's target client, amber PRD v0.8) has split caches: its own
read-only I$ and amber as a write-back D$. On `fence.i` an I$ refill reads
memory, so any dirty D$ line holding the new code must be written back
first. amber's CPU port has no maintenance request today: `l1_pkg` has the
six snoop types but no CPU-side clean or invalidate op.

## What

A CPU-side "clean all" request on amber: walk every set and way, write back
each Modified line (leaving it clean and valid), and respond when the last
write-back has its B response. Invalidate is not needed; peregrine
invalidates only its I$.

## Done when

- The request is in amber's CPU-plane contract (HAS/MAS) and the GAXI
  request encoding.
- A directed test dirties lines across sets and ways, cleans, and checks
  memory against the scoreboard; the FULL grid stays green.
- peregrine's rv32ui `fence_i` and arch-test `Zifencei` pass at
  `CACHE_EN=1` (riscv-ip/peregrine-rv32im TASK-001 stage 4).

## Not decided here

Whether the walk reuses the snoop `CLEAN_SHARED` drain path or a separate
sequencer is amber's MAS call.

## Design (2026-11-24)

Decided here (the MAS carries the detail: ch02_blocks/01 "Clean-all walk",
ch03_interfaces/01 Table 3.1.2, ch03_interfaces/03 write table):

- **Request encoding.** A `maint` bit above `addr` on the CPU GAXI request,
  `{maint, addr, we, be, wdata}`, behind a `MAINT_EN` parameter on
  `l1_cpu_frontend` / `l1_cpu_plane` / `amber_top` / `amber_ace_top`
  (default 0: the classic packing, so jet, jet-prime, `l1_core`, the
  Genesys2 board harness and every existing amber consumer are unchanged).
  `maint = 1, we = 0` is the clean-all; `maint = 1, we = 1` is reserved.
  The response (one, after the last B) echoes `wdata`. An in-band encoding
  (a write with `be = 0`) was rejected: `be = 0` writes are a tested
  l1_control contract (MINOR 2) and random TBs generate them.
- **Sequencer, not the snoop CLEAN_SHARED path.** A clean-all needs a memory
  write per M line and its B before the response: that is the miss path's
  gather + `l1_drain` + `drain_done`. Four new states
  (`CTRL_CLEAN_SCAN/GATHER/COMMIT/RSP`, codes 0xC-0xF) add the scan (which
  line: cursor set ascending, the lowest M way first) and the commit
  (M -> E). The drain itself is `CTRL_MISS_DRAIN`, unchanged except for the
  exit (to the commit) and `ctrl_drain_clean`.
- **WriteClean, not WriteBack.** ACE WriteClean (AWSNOOP 0x2) keeps the
  line; WriteBack evicts. The coherence sideband reports a new
  `AMBER_ACE_WRITE_CLEAN` (3'b111); `l1_ace_issue` latches the drain
  launch's class and stamps the drain engine's AWSNOOP; the pair fabric and
  onyx's `is_coh_req` treat it as a write-port pass-through like WRITE_BACK.
- **The line stays installed while its write-back is in flight.** The
  victim-buffer snoop bypass (which owns an evicted line until its B) is off
  for a clean drain; a snoop resolves on the installed M line, reads the
  unchanged data array, and writes its downgrade there. The commit only
  writes E if the way still holds the line at M.
- **Snoop progress.** `CTRL_CLEAN_SCAN` is snoop-safe and visited once per
  set and after every cleaned line; `CTRL_MISS_DRAIN` stays snoop-safe. The
  TASK-005 hit path (`HIT_RUN_MAX`, the 1-cycle hit) is untouched: a
  clean-all never takes the accept-cycle fast path, `CTRL_LOOKUP` routes it.
- **MonBus.** A clean write-back is DRAIN_START / DRAIN_END and its commit
  a TRANSITION (cause 7); not an EVICT (`l1_coh_core` gates the victim-load
  tap with `ctrl_drain_clean`).

## Progress (2026-11-24): implemented, not yet committed

RTL: `l1_pkg` (states 0xC-0xF, `AMBER_ACE_WRITE_CLEAN`), `l1_control` (the
walk, `req_maint` in, `ctrl_drain_clean` out), `l1_cpu_frontend` /
`l1_cpu_plane` (`MAINT_EN`, `req_maint`), `l1_coh_core` (seam, WRITE_CLEAN
sideband type, monlite taps), `l1_core` (seam, MAINT_EN 0), `l1_ace_issue`
+ `l1_ace_plane` (WriteClean AWSNOOP), `amber_top` / `amber_ace_top`
(`MAINT_EN`, default 0), `amber_pair_fabric` and `onyx_ccu` (WRITE_CLEAN is
not a coherence request). Tie-offs: `.req_maint(1'b0)` /
`.ctrl_drain_clean()` in every direct `l1_control` harness (common-ip
control / snoop-resp / frontend harnesses, the four amber macro tests);
`.req_maint()` in `jet_cpu_plane` and `jet_prime_cpu_plane`.

Tests: the pair rig harness builds `MAINT_EN = 1` (every rig request
carries the bit; non-clean ones 0). `amber_pair_rig_tb` models the walk
(order: cursor set ascending, lowest M way first, scored at every gather;
the commit M -> E unless a snoop moved the line; WRITE_CLEAN updates the
memory model) and checks the whole DUT tag array against the model after
every clean. New directed scenarios: `CleanAll` (dirty lines across three
sets and every way of one, a clean line, peer dirty lines; every M line
written back once, DUT tags E, memory == cache, the lines then hit with no
fill, a re-dirtied line is the only write-back of a second clean, a third
writes nothing) and `CleanAllWithSnoops` (four rounds of peer traffic on
the lines being cleaned at staggered starts, plus three targeted rounds
where the peer hits the very line being gathered, so its snoop is granted
while that line's WriteClean is in flight). The func/full random lockstep
issues a clean-all with probability 0.02 per op on either CPU.
`amber_ace_issue_tb` gains WriteClean and WriteBack-after-WriteClean rows.

Mutation pass (pair rig gate, s016w2 and s128w4): 6/6 caught -- commit
writes E after a snoop moved the line; victim-buffer bypass left on for a
clean drain (survived the first pass: no stream snooped the line being
drained; the targeted rounds and the full tag-array parity check were added
for it); walk starts at set 1; clean drain labelled WRITE_BACK; commit
installs S; respond with the last set's M line still dirty.

Formal (`formal/amber/amber_control`, flat regenerated with
`REPO_ROOT=/tmp/rds-canonical-repo-root`, `req_maint_q` exposed): new
safety properties on the tag model `ap_clean_gather_m`, `ap_clean_commit`,
`ap_clean_no_new_m`, `ap_clean_rsp_no_m`, `ap_clean_no_buffer`, and in the
props `ap_clean_rsp_after_b` and `ap_rsp_in_hit` (now with CLEAN_RSP); the
drain partner re-arms at CLEAN_COMMIT as at FILL_WRITE. Covers
`cp_clean_snoop`, `cp_clean_commit_wr`, `cp_clean_rsp_after_wr`. Liveness:
`req_maint` free, `ap_clean_scan_bounded` (< 17), `ap_clean_gather_bounded`
(< 10), `ap_clean_single`; a clean-all is exempt from `ap_txn_bounded`
(free tags make its length unbounded; the safety tag model carries
termination). Cover (depth 80) PASS 12/12 (clean covers at steps 21, 42,
59). Liveness (depth 126) PASS; a one-off cover on the liveness wrapper
reached `cp_clean_scan_long` and `cp_clean_done` (step 36). Formal mutants
(BMC depth 44): commit installs S -> `ap_clean_commit` fails; bypass left on
-> `ap_clean_no_buffer` fails at step 39.

Regressions (clean-all, 0 reruns): common-ip FULL 255/255 (seed base
3705241571), amber-mesi-l1 FULL 121/121 (1262453800), jet-mesi-l1 gate
19/19 (558088070), jet-prime-mesi-l1 gate 21/21 (3827303412), onyx-ace-ccu
gate 12/12 (1587938542); peregrine `test_peregrine_amber_latency` pass (hit
1/1, write 1/2 unchanged).

OOC (Genesys2 xc7k325t-2, `amber_top`, 10 ns, scratchpad builds):
MAINT_EN=1 WNS +0.357 ns, 3,766 LUT / 2,866 FF / 16 RAMB36 / 1,169
LUTRAM; MAINT_EN=0 WNS +0.696 ns, 3,773 LUT / 2,857 FF. (TASK-005's build:
+0.342, 3,579 / 2,857.) Worst path unchanged in kind: `u_control/state_q`
into the monlite queue. The walk costs ~190 LUT whether or not MAINT_EN is
set (the states stay in l1_control; synthesis does not prune them from a
tied-0 `req_maint`).

Safety BMC (depth 48): PASS, launched 2026-11-24 18:07, done 19:03
(56 min wall, boolector, no trace).
## Closed (2026-11-24)

The last "Done when" line holds: peregrine TASK-001 stage 4 wired amber
(`MAINT_EN=1`) as its D$, fence.i issues the clean-all before the I$
invalidate, and at `CACHE_EN=1` rv32ui `fence_i` passes in spike lockstep
and riscv-arch-test `Zifencei` (Fencei) passes its signature, which the TB
reads from memory after a clean-all through peregrine_top's hook. Both at
gate, func and full (peregrine FUNC 57/57 seed base 1677929868, FULL 85/85
seed base 3310830104, 0 reruns); peregrine's `smc_basic.s` adds
self-modifying code through dirty amber lines. A mutant with the clean
stubbed out fails smc_basic, Fencei and rv32ui `fence_i`.

Seen from peregrine, not changed here: amber installs every read fill
Shared (the AXI4 plane has no IsShared), so in a one-cache system each
first store to a loaded line pays a CleanUnique upgrade.
