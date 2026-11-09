---
title: Resolve the select at the load, not in front of the consumer
summary: A 2:1 mux of two register sets by a registered decision bit is one LUT level plus a high-fanout net at the ROOT of every consumer; load one register set with the decision at its D input instead. The fire cone it was kept off the load path to protect was never the long one. mc_bank_pick, granite 100 MHz, 2026-11-08.
---

# Resolve the select at the load, not in front of the consumer

**Rule:** when a stage keeps two (or three) candidate register sets and a
registered bit that says which one is current -- "the held winner or the
fresh pick", "the shadow or the record" -- and a wide cone reads the muxed
result, move the select to the register's D input: ONE register set, loaded
with the value the mux would have produced. The consumer then reads flops.
The behaviour is identical cycle for cycle (the register holds exactly what
the mux produced), which is what the equivalence proof confirms.

The mux-in-front form is usually chosen to keep a late decision OFF the
register's load path ("no fire-cone term on any load path"). Measure that
decision's own slack before paying for the rule: the cone the mux feeds is
often the longer one, and the net the mux drives is the widest in the block.

## The failure that taught it (mc_bank_pick, granite 100 MHz, MC-011)

The pick core served its fire stage from `r_hold ? r_held_* : r_pick_*`
(three register sets, a hold bit), and the request mask from a 3:1 mux of
three registered masks by the hold and speculation bits. That kept the fire
cone off every load path -- and put one LUT plus two long nets (0.87 and
0.90 ns; the mux output fanned out to ~90 loads: the rotor search, the
candidate mux, the bank of the live timer read) at the ROOT of every
arbiter-cone path. Every failing arbiter path on the 100 MHz board build
started there: -0.276 ns, 11 levels, 80 percent of it wire.

Resolved at the load (`r_win_*`, `r_self_stale`): the hold decision selects
between the current winner, the speculation and the fresh pick at the D
input. The fire cone gained one mux level on a path with over 0.4 ns of
slack; the arbiter cone lost its root. With the registered compares of
[[registered-status-outputs]] and a per-source class instead of a 16:1 mux
behind the index encode, the build went from 179 failing endpoints to none
under the 0.2 ns budget.

**Reviewer's tell:** a comment that says a mux exists "so that no late term
sits on a register's load path". Ask for the slack of that load path; if it
has margin, the mux is in the wrong place.

Related: [[priority-logic-depth]] (the serialized form of the same mistake
inside one cycle), [[decision-stage-reads-the-snapshot]] (the register IS
the truth; do not read around it), [[formal]] (golden-copy equivalence as
the gate for any such restructure).
