# TASK-003: First consumer selection (PRD D10)

**Priority:** P3
**Status:** deferred 2026-10-02 -- pending a memory controller project consumer
**Owner:** TBD

Filed at the close of reed-solomon TASK-001. PRD D10 has no consumer today.
Sean's direction (2026-10-02): consumers for this IP will come in the future,
probably on a memory controller project. Until one lands, the codec's profile
stays the reference RS(255,239) / RS(252,236)-on-the-harness shape and the PRD
stays a draft.

## Named condition

A memory controller (or other) project names the RS codec as its ECC layer.
That is what un-parks this item.

## What this item does when it wakes

- Pin the profile from the consumer's numbers: m and t (D1/D2 are parameters,
  but the consumer fixes their values), n / shortening (D3), and the
  throughput target that finishes D6 (`SYMBOLS_PER_BEAT` from the consumer's
  clock and rate).
- Fix the generator conventions to the consumer's standard (D8): primitive
  polynomial, first root b, dual-basis if it is CCSDS-shaped.
- Decide whether erasure decoding (TASK-002) is pulled in -- a memory
  controller with known-bad-column support is exactly the D5 consumer.
- Take the PRD to v1.0 (its header: it becomes v1.0 when a consumer fixes
  section 3) and re-baseline the DV matrix on the pinned profile.

## Notes

The encoder-only shape (D4, decided: both viable) is the likely landing for a
transmit/write-only path; the full codec otherwise. No work before the
condition fires -- the component is complete and board-proven at its
reference profile.
