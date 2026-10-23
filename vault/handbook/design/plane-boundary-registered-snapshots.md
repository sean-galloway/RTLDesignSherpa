---
title: Plane boundaries carry registered snapshots, never combinational probes
summary: A plane's internal state (arrays, open rows, timers) never leaves the plane as a combinational input to another plane; plane-to-plane signals are registered snapshots plus handshakes, and a flag that depends on two planes' state is computed in the plane that owns the decision. The -35 ns memory-controller build that taught it.
---

# Plane boundaries carry registered snapshots, never combinational probes

**Rule (owner, 2026-10-19; promoted to the handbook 2026-10-21):** a plane's
internal state -- FIFO arrays, entry registers, open-row images, timer
counters -- never leaves the plane as a combinational input to another plane.
What crosses a plane boundary is a **registered snapshot** (a record that
changes only on a defined event: push, pop, tick) plus **handshakes**. A flag
that needs state from two planes (for example "this entry's row is the open
row") is computed in the plane that **owns the decision**, from its own
register and the snapshot it received.

See [[what-is-a-plane]] for what a plane is; this note is the timing half of
its "data-flow contract at the edges".

## The failure that taught it

The memory-controller family's per-bank scheduler core (MC-003, 2026-10-18/19)
read its sixteen per-bank head views **combinationally** out of the storage
plane: pointer-indexed FIFO reads (`r_row[r_rptr]`), a global age-minimum
compare tree over all sixteen, the arbiter, a 16:1 payload mux and the live
JEDEC fire gate, all in one cycle feeding the winner register -- and the
winner register's own output fed back into the selection. 53 to 56 logic
levels, ~1,300 wires crossing the boundary, 80% of the path in routing
because the placer could not co-locate two planes' logic.

| core | boundary | 75 MHz post-route WNS |
|---|---|---|
| FRFCFS + CAMs | registered per-entry vectors | +0.12 ns |
| per-bank, seat-pending | comb head scans across the boundary | -1.35 ns |
| per-bank, registered pick | comb heads, pick registered | -3.94 ns |
| per-bank, aged matrix | comb heads + age-minimum + payload mux, one cycle | **-33.4 / -35.6 ns** |

Three placement campaigns moved the aged core by 0.3 ns. The structure was
the problem, not the placer. Evidence trail:
`vault/tracking/projects/components/mem-ctrl-ip/MC-003_read_hang_root_cause.md`
sections 11 to 17.

## What the rule looks like in RTL

- **The storage plane presents records, not arrays.** `mc_bank_head_records`
  (`common-ip/rtl/fub/`) derives, per bank, the oldest and second-oldest
  schedulable entry from a backend's per-entry vectors and age matrix and
  **registers** them as `mc_head_rec_t` (`mc_common_pkg`). The scheduler
  plane's decode starts one flop away from that record, inside its own
  plane. Any backend (CAM, entry store, per-bank FIFO) that produces the
  same record is a drop-in.
- **Hit classification rides in the record, against a REGISTERED row
  image.** The record carries row, column and a `hit` flag that the storage
  edge computes against the scheduler plane's own registered open-row /
  row-active flops (`bank_row_active_i`, `bank_open_row_i` on
  `mc_bank_head_records`): register in, register out, one crossing, and the
  flag is one cycle stale by construction. The consumer ANDs it with its
  live row-active bit at fire and never recomputes the row compare. Two
  earlier forms both failed timing: the original contract computed
  `*_bh_act_o` inside the store from the scheduler's open row (comb in, comb
  out, two crossings in one cycle), and the Phase 2 landing compared the
  record's row against the live open row inside the scheduler (a 16:1
  record mux feeding a row compare feeding the arbiter: the worst 75 MHz
  post-route cone, -3.2 ns). Phase 3 (2026-10-22) moved the compare to the
  storage edge; its staleness is paid by the consumer's speculation (below).
- **Handshakes are flop-to-flop.** `wr_commit`, `rd_issue`, `rt_alloc`,
  tickets: a valid/ready pair where both sides register.
- **The cost is one cycle at the boundary**, absorbed by a registered-winner
  scheduler: the winner is decided a cycle before it fires, so a push that
  becomes visible a cycle late is never on the critical loop. The winner
  that waits on a timer HOLDS -- but as a register-to-register mux, never a
  load enable: the pick register loads every cycle, a second register keeps
  last cycle's effective winner, and a registered "waiting" bit selects
  between them in front of the fire stage. A hold implemented as the load
  enable put the whole fire cone on the winner register's load path, which
  is the arc that made a deeply pipelined core fail timing; a no-hold core
  (re-arbitrate every cycle, search past the fresh pick) fired out of
  request order under tCCD and re-picked the stale request in the fire
  cycle. The hold is bounded by the winner's lookahead bit, so a bank gated
  longer than the pipe depth releases it. The pop side costs bookkeeping,
  not latency -- see below.

## What the one-cycle lag costs the consumer, and how to pay it

A registered snapshot is one cycle behind the state it describes. The
consumer that lives one register away cannot pretend otherwise; two things
follow, both learned landing `mc_bank_pick` on the record contract
(2026-10-22):

- **The pop shadow.** In the cycle after the consumer pops an entry, the
  record still shows it. The consumer remembers WHICH queue it popped last
  cycle (one bit per queue, no slot compare: the slot compare was a record
  mux on the arbiter's path) and, for that one cycle, serves the queue from
  its SECOND record. That is the whole reason the contract
  carries a second record: it is what sustains one command per cycle from a
  single queue. It also means the consumer re-checks the entry it finally
  fires against live state (the entry may be two pops past the one its
  earlier stage classified); the registered decision is advisory.
- **The stale request.** A request register derived from the snapshot lags
  the fire by a cycle too -- and it describes the fired entry for TWO
  cycles, not one: it was decoded from the snapshot the cycle before the
  pick, and again from the snapshot in the fire cycle, which still shows the
  entry (the pop shadow re-aims the candidate that cycle, not the request).
  After a fire that changes what the queue wants next (a row command, or a
  column that empties the queue) the stale request must be masked for both
  cycles, or the arbiter re-picks it and the fire stage drops it -- measured
  once as every other cycle wasted on a bank-rotating write stream (the
  first cycle), and once as a free slot every burst that the page policy's
  idle-timeout close took to shut another requester's open row, one ACT per
  eight columns and 19% of streaming bandwidth with eight requesters (the
  second cycle; mem-ctrl recovery Phase 3 follow-up, 2026-10-22). Both
  masks are registers: the first from next cycle's known winner, the second
  from the fire itself, keyed on the fired entry's "nothing behind" flag.
  The consumer knows which fire does this; it masks that one queue, not the
  request vector. A free slot is never harmless when something is waiting
  to use it: trace what fired INTO the slot before calling it a bubble.

Both are consumer-side bookkeeping, a handful of flops. Neither is a reason
to move the pop or the decision back across the boundary.

## A consumer takes its event from the edge its state updates on (2026-10-22)

`mc_page_policy` compared each command against the scheduler plane's
registered bank image (row active, open row) but took the command itself
from the plane's command FIFO's READ side. The image updates when a core
FIRES into that FIFO; the read side is that fire plus the FIFO's occupancy,
an arbitrary number of cycles later. So the policy saw every PRE after the
row image had already dropped and its own expired flag had cleared: timeout
closes counted as conflicts, the idle timer re-warmed late, and a predictor
built on "that PRE was a timeout close" never armed -- while the design
being judged (the FR-FCFS core) was innocent (pumice BUG-030). No shadow
register fixes a variable skew; the fix was to feed the policy from the
fire side, the same edge the image it compares against is written on. The
rule: when a block compares an event against registered state, both must
come from the same edge of the same handshake, or the block is measuring
the FIFO.

## How to check a design against it

1. For every edge in the plane diagram, name the register that drives it.
   An edge whose driver is an `assign` from an array element or a scan over
   array elements violates the rule.
2. For every flag computed from two planes' state, name the plane that owns
   the decision; the flag lives there.
3. In a timing report, a failing path whose startpoint and endpoint are in
   different plane hierarchies is this rule being broken, whatever its
   logic depth.

Related: [[what-is-a-plane]], [[registered-status-outputs]],
[[priority-logic-depth]], [[block-boundary-dead-cycles]].
