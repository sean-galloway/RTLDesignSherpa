# TASK-005: pipelined hit path on amber's CPU port, for peregrine's MEM stage

**Priority:** P2
**Status:** open
**Owner:** TBD (filed from riscv-ip/peregrine-rv32im PRD P13; the owner chose
option (b), "amber gains a pipelined hit path", on 2026-11-24)

## Why

peregrine (amber's target client, amber PRD v0.8) uses amber as its D$.
peregrine TASK-001 stage 6 measured amber's CPU-side hit timing on the pair
rig at the l1_pkg default geometry
(`projects/components/riscv-ip/peregrine-rv32im/dv/tests/test_peregrine_amber_latency.py`):

| Access | Response valid (cycles after accept) | Port ready again |
|---|---|---|
| Read or write hit | 4 | 3 |
| Write to an S line (CLEAN_UNIQUE upgrade) | 18 | 17 |
| Miss (bench memory) | 29 | 28 |

The hit path is IDLE (accept), LOOKUP (tag read), HIT_RD/HIT_WR, IDLE with
ready high, and then the response leaves the 2-deep staging FIFO
(`l1_cpu_frontend`, DECISION D-6). In a 5-stage core that waits in MEM,
that costs about 3 cycles per access over a 1-cycle hit: about 1.1 CPI at
0.36 accesses per instruction, more than the whole miss term in peregrine's
CPI model (PRD §4.8).

## What

A hit path that can take a new CPU request every cycle and return a hit's
response at a fixed, short latency, without changing the miss, snoop or
coherence behaviour.

- **Precedent in this repo:** jet-prime reached a 2-cycle hit floor with
  one hit per cycle from depth 4 (jet-prime PRD JP2/JP7;
  `jet-prime-mesi-l1/docs/delta/04_two_cycle_hit.md`). Read that before
  designing; amber stays blocking on a miss, so only the hit pipeline
  carries over.
- **Target latency** is part of this task's design, together with
  peregrine stage 4. 1 cycle (response valid the cycle after the accept)
  lets peregrine keep a single MEM stage. 2 cycles needs either a split
  MEM (M1/M2) or one stall per access in peregrine. Measure what 100 MHz on
  xc7a100t-1 allows before choosing.
- A hit issued behind an older hit to the same line must see that hit's
  write (store then load, the commonest pair).

## Done when

- The hit pipeline is in amber's HAS/MAS (CPU-plane contract and timing).
- peregrine's `test_peregrine_amber_latency.py` `EXPECT` table is updated to
  the new hit latency and occupancy and passes.
- amber's FULL grid stays green: the pair rig, the ACE top, the macros and
  parity.
- amber's OOC timing still closes at 100 MHz.

## Not decided here

- Whether the staging FIFO stays or the hit response bypasses it.
- 1 versus 2 cycles (see above).
- Whether the change lives in common-ip `l1_control` or `l1_cpu_frontend`.
  `l1_control` is the shared common-ip core; check its other users before
  changing its contract.
