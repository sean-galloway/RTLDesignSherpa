<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# jet-prime delta 02: the pipelined pair fabric (TASK-001 step 3)

**Status:** landed 2026-11-16. The second place jet-prime's architecture
differs from jet's. jet's books ([HAS](../../../jet-mesi-l1/docs/jet_has/jet_has_index.md),
[MAS](../../../jet-mesi-l1/docs/jet_mas/jet_mas_index.md)) still describe
the cache; this chapter records what changed in the pair fabric and the two
sidebands that carry it, and why. [Delta 01](01_fill_engine.md) is the
fill engine this fabric exists to feed.

## What changed, in one paragraph

jet's `jet_pair_fabric` ran one coherence transaction at a time: grant,
snoop the peer, then the memory read, then the next grant. With several
fills in flight per cache (delta 01) that serial fabric was the whole gap
to HPDcache a peer could re-open: step 1 measured it at 2.5 cycles per
transaction on the 64 KB thrash, a quarter of jet's miss cost, with the
peer idle. `jet_prime_pair_fabric` serializes **per line**: a transaction
table holds every request in flight, a request waits only behind an
in-flight transaction on its own line, the memory read is issued alongside
the snoop and its data dropped when the peer supplies the line, and one
AXI read ID per table slot keeps several memory reads outstanding. The
amber-era kill rule, drain guard, upgrade-priority grant and peer-state
wait are gone; a retire sideband from the cache (`coh_done_*`) replaced the
pseudo-state inputs as the fabric's only knowledge of the cache's commit.

## The transaction table

`rtl/top/jet_prime_pair_fabric.sv`, parameters `FAB_SLOTS` (default 16; the
pair rig and the board harness set `2 * (MSHR_COUNT + 1)`, so no request
ever waits for a slot) and `SNOOP_INFLIGHT` (default 2).

| Slot field | Set by |
|---|---|
| `dir`, `line`, `type`, `nodata` | the grant |
| `ar_taken`, `arid`, `arcache/prot/user` | the requester's AR handshake (grant + 1) |
| `ac_done` | the peer accepting the AC |
| `cr_done`, `dt`, `pd` | the peer's CR (pairs with the AC by order) |
| `mem_issued`, `mem_done` | the memory AR / the last memory R beat consumed |
| `rpl_done` | the last replayed beat (DT line or the upgrade's no-data beat) |
| `abs_issued`, `abs_done` | the PassDirty absorption's AW / BRESP |
| `rack` | the requester's `coh_done` pulse naming the slot's read ID |

A slot frees when the requester has every beat, the memory read (if one
was issued) is drained, the absorption (if any) has landed, and the retire
has been seen. The memory read ID **is** the slot index; the requester's
own ARID is kept in the slot and returned on its R beats, so a cache sees
exactly the IDs it issued (beats of different slots may interleave per ID,
which the fill engine handles).

### Grant

Per direction a small queue holds the D-8 request pulses in order (the
cache's read transport skids ARs, so a cache can run a few launches ahead
of the AR this fabric holds; pulses and ARs stay in launch order). The
head is granted when **no valid slot holds its line** and a slot is free;
a live pulse is granted the cycle it arrives when the queue is empty. The
two directions round-robin when both heads are ready. The grant allocates
the slot and arms the AR take: `arready` to that cache is asserted the next
cycle, from registers only, and the AR's line is checked against the
slot's (a simulation assert). Only now does the requester's entry become
post-AR at the cache.

### The snoop and the memory read

Each grant queues the slot on the **peer's** snoop queue; the AC is
presented in grant order with up to `SNOOP_INFLIGHT` accepted-not-answered
(the responder serves one at a time, its transport skids the next). CD
beats land in the slot's line buffer (one LUTRAM array per peer indexed
`{slot, beat}`: one write port each, two read ports -- a single array
written from both peers has two write ports and came out of the first
build as 9 k flops behind 272:1 muxes, 35 k LUT); the CR pairs with the
oldest outstanding AC and records the verdict.

The memory AR for a data fill is issued **once the peer has accepted the
AC**, not when the CR is back, so with an idle peer the verdict lands a
cycle or two before the first memory beat and nothing stalls. A beat that
arrives before its verdict holds the memory R channel for the bounded
remainder of the responder's service; issuing at AC-accept rather than at
grant keeps that stall bounded by the responder, never by a peer's commit
backlog. A verdict of DataTransfer that lands before the AR issued
suppresses it; one that lands after -- on a presented or an issued AR --
drains the beats and drops them.

A presented memory AR is **held until the memory takes it** (AXI A3.2.1).
The candidate is the lowest-index slot ready to issue, and the step-3 build
re-pointed a stalled AR at a lower slot whose AC had just been accepted:
`ARVALID` high, `ARID`/`ARADDR` changed. The fabric formal's
`ap_mar_stable` found it in its first second (step 4); the pair rig and the
board had not, because the memory's two-deep burst queue rarely stalls the
AR and nothing on the memory side checked the AR's stability -- the rig's
monitor does now. With the hold, a DataTransfer verdict landing on a held
AR no longer marks the read done early: the AR goes out and its beats are
drained like any other dropped read.

### Delivery

Per direction the R channel carries memory pass-through beats (verdict:
no DataTransfer) and replayed beats (the buffered CD line, or an upgrade's
single no-data beat). The memory beat has priority (the memory R channel
is the shared resource), the replay fills the gaps, and a presented replay
beat holds until accepted (AXI payload stability).

### Write port

One burst at a time, round-robin over {cache 0 write-back, cache 1
write-back, absorption}. The absorption writes a PassDirty line from the
slot buffer with AWID `8'hA0 | dir`. A write-back AW to a line **holds
while a slot on that line has no CR yet** or an absorption to it is
pending. The hold is defensive, not load-bearing: the memory AR issues
only after the peer has accepted the AC (`ap_mar_legal`, proven in step
4), and `l1_snoop_resp` latches the verdict at that accept -- so the
verdict is decided before any read of the line reaches memory. A
write-back still in the peer's buffer at the accept answers DataTransfer
from its snapshot (the ships-in-the-night scenario); one already retired
has its BRESP, so its data is in memory before a read issued after that
accept. The hold stays because it is bounded by the snoop service and
costs nothing on the measured rows; it is checked as written
(`ap_wb_select_hold`), at the cycle the write port picks the write-back.

## Why the lock is pulse-to-retire

The cache's pre-AR rule (jet MAS ch02/05) answers a snoop to an entry
whose AR has not been taken at the Invalid row with no effect: that is
what keeps a same-line loser answer-neutral, and it is the fabric that
makes the loser pre-AR by holding its AR. The question is when the winner
is "done" enough for the loser to proceed. Not at its last beat: between
the last R beat and the entry's retire the winner is post-AR with beats
landing, and a snoop then is answered from the pending-fill bypass with
the post-fill state and (PF_GUARD) no data -- an answer that orders the
snoop after a fill that must stay ordered before it, and for a write fill
would discard the merge at the deferred invalidate. The responder's own
`sn_safe` hold (any done-but-unretired fill) covers most of that window;
the retire sideband closes it exactly. So:

- `jet_prime_control` gained `cu_done_o` (the upgrade's deposit cycle).
- `jet_prime_coh_core` / `jet_prime_top` export `coh_done_valid` /
  `coh_done_id`, registered like the request pulse: one pulse per retired
  MSHR entry (its index, which is its read ID) or completed upgrade
  (`MSHR_COUNT`, the upgrade slot's ID). The ACE top leaves them
  unconnected; its transport carries RACK.
- `lkup_live` and the `ctrl_state` consumers in the fabric are gone (the
  signal the BUG-004 fix struck from one grant rule is now read by no
  rule).

Same-line conflicts are therefore still grant-after-completion, where
completion now means the winner's retire. The cost is that the loser's
cache holds its AR register behind the conflict for the winner's lifetime,
which also holds that cache's later launches -- bounded, and the price of
keeping the loser pre-AR without a replay path.

## Liveness

Every wait resolves on an agent that does not wait on this fabric:

- a CR: the responder grants whenever its own commits have retired, and a
  commit needs only beats that have landed (never the fabric);
- the requester's `rready` and retire: local;
- the memory: in-order, two bursts queued per direction;
- the write port: round-robin among three candidates, each bounded.

No wait looks at a peer's lookup or pseudo-state; the handbook rule from
BUG-004 ("walk every hold and name the agent that releases it") is what
removed them.

## Verification that carries this step

- `test_jet_prime_pair_rig`: the fabric layer of the lockstep model keys
  live transactions by (direction, line), scores every AC against the
  live transaction of the other direction on that line (type, address,
  one snoop per transaction, at most `SNOOP_INFLIGHT` outstanding), CR/CD
  per peer in AC order, the memory read by slot (issued only after the AC
  was accepted, never for an upgrade, never twice; a DataTransfer fill's
  read dropped or suppressed, a pass-through read completed), the grant
  order and the per-line rule at every grant, and the slot release only
  after the retire. Scenario (a) now checks the forwarded fill's memory
  read was dropped or suppressed instead of "never issued"; scenario (i)
  runs eight concurrent fills per cache through the pipelined path.
- Core, parity and control suites: unchanged in substance (the control
  harness and the formal wrappers wire the new `cu_done_o`).
- `formal/jet-prime/jet_prime_control`: the flat regenerated for the new
  output; safety prove PASS on it (boolector, 11:57 wall); the liveness BMC
  (depth 192) and the covers were still running at the step-4 commit and
  are recorded in TASK-001 when they land.
- `formal/jet-prime/jet_prime_pair_fabric` (step 4): the fabric alone at
  the tiny geometry (16-bit addresses, 16-byte lines on a 32-bit bus,
  `FAB_SLOTS` 4, `SNOOP_INFLIGHT` 2), both caches, both responders and the
  memory free inputs under their documented contracts (the harness header
  is the assumption inventory: launch order and one read ID per entry on
  the AR, the retire after the last beat, CR/CD only for an accepted AC
  with the CD beats before a DataTransfer CR, memory beats only for an
  issued read). Twenty-seven safety properties: one valid slot per line and
  no grant to a held line (the per-line rule), the lock dropping only
  after the requester's own retire pulse and only once the requester has
  its last beat and the read is drained, one AR take per grant with the
  slot's line and class, the memory AR only after the AC accept and never
  for an upgrade or twice, every R beat routed to its direction with the
  requester's own ID (a memory beat never for a DataTransfer slot), exactly
  the beats each AR asked for, AC/CR/CD bookkeeping, the write-back hold
  at selection, the absorption's address and ID, no pending-queue overflow,
  and AXI/ACE valid-payload stability on every channel the fabric drives
  (memory AR, both R channels, both ACs). Nineteen covers, all reached by
  step 14 (two directions live, three slots live, a same-line conflict
  waiting and re-granted on the freed line, a DataTransfer read dropped
  and one suppressed, a replay behind a memory beat, the absorption landed,
  a write-back held and then landed, two snoops outstanding, two reads
  outstanding, a memory AR stall). Ten mutations, each failing the property
  written for the mechanism it breaks (the lock, the retire gate, the
  replay hold, the memory-AR hold, the early-done rule, the write-back
  hold, AR-before-AC, a second grant per direction, the R routing). The
  proof is BMC, claimed as such: 24 properties to depth 24 (a same-line
  request waiting out a whole PassDirty lifetime and then taking its own
  AR is ~24 steps), the three end-to-end bookkeeping properties (IDs in
  flight, beats per ID, the CD beat's slot) to depth 16 -- their cost grows
  2.5x per step where the rest grow 1.3x, because refuting them means
  carrying the whole trace. Three more properties came out of a
  k-induction attempt that did not close: the cache's untaken launches
  equal the fabric's pending pulses plus the one awaiting its AR; every
  slot flag implies the flags before it in the slot's life; every engine's
  held slot is live in the matching phase.
- The Genesys2 reference rig at `REF_CACHE_SEL=3` (flow
  `ref_jetpp_bringup`): two jet-prime caches through this fabric, one per
  injector -- the jet rig's structure with jet-prime's RTL. Its ci1-idle
  row against SEL 2 is the fabric's cost to a single core; against the jet
  rig's row, the rebuild's gain. Numbers in TASK-001's progress log and the
  [reference comparison](../../../docs/reference_l1_comparison.md).
