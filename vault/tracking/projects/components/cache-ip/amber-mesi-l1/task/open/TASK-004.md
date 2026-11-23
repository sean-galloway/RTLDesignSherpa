# TASK-004: CPU-side clean-all request for peregrine's fence.i

**Priority:** P3
**Status:** open
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
