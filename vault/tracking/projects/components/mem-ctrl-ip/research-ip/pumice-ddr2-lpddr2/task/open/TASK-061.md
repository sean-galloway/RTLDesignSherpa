# TASK-061: age-carrying per-bank FIFO for granite -- the scheduler level below FR-FCFS without CAMs

> Source: owner, 2026-10-25, while TASK-060 was running: "The next level
> below FR-FCFS with cams, is one with out. This requires a new FIFO that
> takes age along with data when an entry is put into it. On the valid/ready
> the age is one more than the current greatest age across the N bank fifos.
> There is a 'age_decr' signal that asserts whenever any fifo has valid/ready
> this moves the age toward 0, where it stops decrementing. I has fully
> specified this before, but I don't see this fifo or anything like it in
> the granite area."
>
> Searched 2026-10-25 before filing: no `age_decr` anywhere in the repo (RTL,
> handbook, trackers, docs, Python); no age-carrying FIFO in `rtl/common`
> (`fifo_sync`, `fifo_control` only); the only "age" in the mem-ctrl trackers
> is pumice's CAM relative age (TASK-001) and the FIFO store's per-slot age
> hook (`HAS_AGE`, compiled out in granite by TASK-059). The earlier
> specification is not in the tree, so the words above ARE the spec of
> record; if the original is found, link it here.

**Priority:** P2
**Status:** open (filed 2026-10-25)
**Owner:** TBD

## The block

`fifo_sync_aged` (name to settle; lives in `rtl/common/includes` conventions
apply): a synchronous FIFO whose entry carries `{age, data}`.

- **Push** (`wr_valid && wr_ready`): the entry's age is written as
  `1 + max(age of the head of every one of the N bank FIFOs)` -- the global
  "greatest age" is an input to every instance (`age_max_i`), computed once
  in the owning plane from the N heads; the FIFO does not know about its
  siblings.
- **`age_decr_i`**: asserted by the plane whenever ANY of the N FIFOs pops
  (`rd_valid && rd_ready` on any instance). On that cycle every stored
  age in every FIFO decrements by one, saturating at 0 (an entry at 0 stays
  at 0). So an age is "how many pops anywhere must still happen before this
  entry is the oldest thing in the bank set", and the heads' ages order the
  banks by arrival without a CAM, a matrix or a free-running counter.
- **Head outputs**: `rd_valid`, `rd_data`, `rd_age` (the head's current age).
  The plane picks the bank whose head age is greatest among the ready
  heads (FR-FCFS's "oldest first" across banks, with row-hit preference
  layered on top by the pick core as today); ties by bank index.
- **Why ages decrement rather than count up**: no counter wraps, no
  subtract per compare, the compare is on small saturating fields, and an
  entry's age is bounded by the total occupancy of the N FIFOs (AGE_W =
  clog2(N x DEPTH) + 1 is enough, with the +1 for the saturation headroom).
- Both directions (a read set and a write set of N bank FIFOs), the same
  block.

## The age bits (owner, 2026-10-25, second message)

Ask for `AGE_W` bits (say 6); the FIFO keeps one more internally, the
OLDEST flag. The 6-bit field is loaded as above and decrements toward 0 on
`age_decr`; when it reaches 0 the 7th bit sets and stays set (the entry has
seen every pop that was ahead of it anywhere). By the way the FIFOs are
loaded and the ages move, **the 7th bit always marks the oldest entries
across all N banks**: an entry with the flag set has no older entry
anywhere, and when any FIFO holds entries at least one head carries the
flag. So the arbiter's FIRST-LEVEL enable is one bit per bank -- the head's
oldest flag across the 8 -- no compare of age fields at all. "All flags 0
while valids are up" cannot happen; if it does it is a bug and goes out as
an ERROR on monbus (TASK-062 puts the monitor on the controllers).

Modes: with age ordering the request vector into the arbiter is the oldest
flags; without it (no FR-FCFS on the FIFO scheme) the request vector is
simply the head valids. One mux, build-time or CSR.

Verification obligations this fixes: (1) the invariant above as an
assertion in the unit TB and the formal block (never a flag-less populated
set; never two different entries older than each other); (2) saturation at
0 holds the flag; (3) the push age `1 + max(head ages)` never overflows
`AGE_W` at the sized depth (N x DEPTH entries bound it).

## Where it goes

granite's FIFO store (`mc_bank_fifo_store`, pumice TASK-050/054) already
keeps per-bank linked-list queues through a shared slot pool and exposes head
records to `mc_bank_pick`. This task adds the age field to those queues (or
replaces the queue structure with N `fifo_sync_aged` instances per direction,
measured both ways), feeds `age_max` / `age_decr` from the plane, and gives
the pick core an "oldest ready head" select keyed on the head ages. The
result is the scheduler level between today's in-order-per-bank pick and
pumice's FR-FCFS: age order across banks, no CAM.

## Measure

Unit test for the FIFO (push/pop/age sequences, saturation, N-sibling
`age_max`); then the granite proxy at 1 / 8 threads and mixed against the
grid, ASAP7 planes, board build + `make smoke` + char. The claim to test is
pumice-like ordering at FIFO-store area.

## What landed / Measured / Gates

(not started)
