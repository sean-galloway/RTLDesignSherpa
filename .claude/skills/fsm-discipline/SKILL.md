---
name: fsm-discipline
description: Minimize state machines, and use NONE on the data path. Use when designing or reviewing any block that moves beats, or before writing a state machine of any size.
---

# fsm-discipline

READ FIRST: vault/handbook/INDEX.md (the handbook is the repo's memory; this skill is the
signpost). Canonical: vault/handbook/design/streaming-no-fsm.md (the datapath
rule) and vault/handbook/design/minimal-fsm.md (the control-path rule).

Two rules, and the first is absolute:

**1. No FSM in the per-beat data path.** Not a minimal one, not a two-state one.
Datapath blocks are valid/ready pipelines: `s_ready = !r_valid || m_ready`,
register the beat, propagate backpressure. An FSM there caps throughput at one
beat per state visit, and forces a separate correctness argument per state for
`m_ready` deasserting mid-beat — which is where the bugs that reach silicon live.

**2. Where an FSM IS right — control paths: descriptor lifecycle, schedulers,
init sequencers, error recovery — keep it minimal.** Fewest states carrying real
distinctions; two-process form with a default-hold; one FSM per module.

The dividing question is not "is this complicated?" but **"does this logic see
per-beat data?"** If yes, it is datapath, and it gets a pipeline.

Before minimizing a machine, ask whether it should exist. The handbook note has
the substitution table (counter for a waiting state, `r_valid` for a mid-burst
state, arbiter for a turn-taking state) and the pumice precedent, where retiring
whole FSMs into counters plus qualifiers came out both simpler and faster.

The handbook root is vault/handbook/INDEX.md - design/, dv/, fpga/, authoring/ areas,
atomic notes, wikilinked. When you learn a durable lesson in this domain,
ADD IT TO THE HANDBOOK NOTE, not to this skill.
