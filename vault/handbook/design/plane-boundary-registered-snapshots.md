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
- **Hit classification is sched-local.** The record carries row and column,
  not "hit"; the scheduler compares against the open-row register it owns.
  The earlier contract computed `*_bh_act_o` inside the store from the
  scheduler's open row (comb in, comb out, two crossings in one cycle).
- **Handshakes are flop-to-flop.** `wr_commit`, `rd_issue`, `rt_alloc`,
  tickets: a valid/ready pair where both sides register.
- **The cost is one cycle at the boundary**, absorbed by a registered-winner
  / hold-on-not-fired scheduler: the winner is decided a cycle before it
  fires, so a push that becomes visible a cycle late is never on the
  critical loop. The pop side costs bookkeeping, not latency -- see below.

## What the one-cycle lag costs the consumer, and how to pay it

A registered snapshot is one cycle behind the state it describes. The
consumer that lives one register away cannot pretend otherwise; two things
follow, both learned landing `mc_bank_pick` on the record contract
(2026-10-22):

- **The pop shadow.** In the cycle after the consumer pops an entry, the
  record still shows it. The consumer remembers {which queue, which slot} it
  just popped and, while the record's head still carries that slot, serves
  the queue from its SECOND record. That is the whole reason the contract
  carries a second record: it is what sustains one command per cycle from a
  single queue. It also means the consumer re-checks the entry it finally
  fires against live state (the entry may be two pops past the one its
  earlier stage classified); the registered decision is advisory.
- **The stale request.** A request register derived from the snapshot lags
  the fire by a cycle too. After a fire that changes what the queue wants
  next (a row command, or a column that empties the queue) the stale request
  must be masked for that cycle, or the arbiter re-picks it and the fire
  stage drops it -- measured as every other cycle wasted on a bank-rotating
  write stream. The consumer knows which fire does this; it masks that one
  queue, not the request vector.

Both are consumer-side bookkeeping, a handful of flops. Neither is a reason
to move the pop or the decision back across the boundary.

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
