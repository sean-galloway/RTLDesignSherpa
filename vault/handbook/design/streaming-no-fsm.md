---
title: Streaming datapaths - no FSM
summary: Skid-buffered pipelines with backpressure, not state machines. On the data path an FSM is a defect, not a style choice.
---

# Streaming, not FSMs

Datapath blocks (engines, movers) are valid/ready pipelines:
`s_ready = !r_valid || m_ready`, register the beat, propagate backpressure.
Skid buffers (`gaxi_skid_buffer`) decouple timing at block boundaries; when
a block gates a handshake (e.g. a monitor's block_ready), the observation
point and the gate must be on the SAME side of the skid or the loop doesn't
close ([[sizing-invariants]] tells the rest of that story).
Reference implementations: stream axi_read_engine / axi_write_engine.

## The rule, stated strongly

**No FSM in the per-beat data path. Not a minimal one, not a two-state one.**
FSMs belong to control: descriptor lifecycle, schedulers, init sequencers,
error recovery. If a state machine can observe a data beat, it is in the wrong
place.

This is stronger than "prefer pipelines", and deliberately so, because the cost
is not stylistic:

- **Throughput.** An FSM that visits a state per beat caps you at one beat per
  state visit. A pipeline sustains one beat per cycle by construction. The
  moment someone asks for back-to-back beats, an FSM datapath needs rewriting
  and a pipeline needs nothing.
- **Corner cases scale with states x backpressure.** Every state must handle
  `m_ready` deasserting mid-beat, and must do it without dropping or duplicating.
  That is one correctness argument per state, and they are the bugs that survive
  to silicon because they need a stall at an exact cycle to reproduce.
- **It hides the elastic buffer.** Backpressure in a pipeline is one expression
  you can read. Backpressure in an FSM is a property of the transition table,
  which is to say it is nowhere.

## What to write instead

The three shapes that replace almost every datapath FSM:

| Instead of a state that... | Write |
|---|---|
| counts beats, or waits N cycles | a counter plus a comparator (`counter_bin`, `counter_load_clear`) |
| remembers "I am mid-burst" | a `r_valid` flag on the pipeline stage |
| serializes because a resource is shared | an arbiter (`arbiter_round_robin`) and a qualifier, not a turn-taking machine |
| gates until a condition holds | a qualifier ANDed into the handshake |

**Precedent:** pumice retired whole FSMs — the bank timer and the CAM control —
into counters plus qualifiers, and the result was simpler AND faster. That is the
usual outcome. Before minimizing a state machine, ask whether it should exist.

## Where an FSM IS right

Control paths, where the block genuinely has modes with different successors:
descriptor lifecycle, schedulers, init and calibration sequences, error
recovery. There, keep it minimal and idiomatic — see [[minimal-fsm]].

The dividing question is not "is this complicated?" but **"does this logic see
per-beat data?"** If yes, it is datapath, and it gets a pipeline.

Related: [[valid-ready-contracts]] for the handshake rules a pipeline must obey,
[[minimal-fsm]] for the control-path case, [[signal-prefixes]] for `r_`/`w_`.
