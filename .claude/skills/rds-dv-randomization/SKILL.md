---
name: rds-dv-randomization
description: Delay/traffic randomization in RDS-DV - the 19 named FlexConfigGen profiles, which layer to use, and the rule that randomized traffic does NOT prove fairness or arbitration correctness. Use when shaping stimulus timing, writing an arbiter/scheduler/picker test, or choosing a delay profile.
---

# rds-dv-randomization

READ FIRST: docs/handbook/INDEX.md (the handbook is the repo's memory; this skill is the
signpost). Canonical: docs/handbook/dv/randomization.md.

ONE OF THREE ORTHOGONAL AXES (see rds-dv-axes): BFM = who drives
(rds-dv-bfms); SEQUENCE = what traffic (rds-dv-axes); RANDOMIZATION = what
timing. Authoritative docs: <RDS-DV>/docs/components/shared/components_shared_flex_config_gen.md
and per-family components_<family>_randomization.md (axi4 has one).

Three layers, pick by what you configure: **FlexConfigGen** (named delay
profiles - start here), **FlexRandomizer** (the engine, for constraint shapes
no profile expresses), **RandomizationConfig** (per-field packet modes, not
delays).

List profiles instead of guessing:
`from CocoTBFramework.components.shared.flex_config_gen import DEFAULT_PROFILES`
19 exist. `backtoback` = zero delay = full saturation. Others worth knowing:
`fast`, `constrained` (general default), `bursty`, `stress`, `slow`,
`heavy_pause`, `chaotic`.

**RANDOM TRAFFIC DOES NOT PROVE FAIRNESS.** Random profiles leave gaps, so a
picker is never cornered and the request pattern decides who is served. A real
round-robin arbiter that starved 2 of 4 clients passed its randomized fairness
phase. For any arbiter/scheduler/picker: saturate deliberately, assert on
PER-CLIENT outcomes (a Jain index > 0.3 on 4 clients passes with two starved),
and mutation-check the assertion.

Two framework gaps recorded in the note: `ArbiterMaster` has its own private
profiles with no saturating option (use `force_client_request`), and
`ArbiterCompliance.analyze_round_robin_compliance()` is a stub returning
`rr_efficiency: 1.0` unconditionally.

The handbook root is docs/handbook/INDEX.md - design/, dv/, fpga/, authoring/ areas,
atomic notes, wikilinked. When you learn a durable lesson in this domain,
ADD IT TO THE HANDBOOK NOTE, not to this skill.
