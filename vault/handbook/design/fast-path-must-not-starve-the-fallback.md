---
title: A fast path must not take the resource its own fallback needs, and the floor is not the measurement
summary: jet-prime's 2-cycle hit gave the arriving request the data port in its capture cycle; the first cut let that lead pre-empt an occupant that could not take the fast path, so that request fell to a slower fallback and a one-deep record stalled the pipe -- the hit floor read 2 while mixed resident rows lost 40 % of their throughput at depth 4+. The fast path yields whenever the fallback would need the resource, and the sweep rows that exercise the fallback are the measurement.
---

# A fast path must not take the resource its own fallback needs, and the floor is not the measurement

**The case (jet-prime TASK-002, 2026-11-19).** The resident read hit went
from 3 cycles to 2 by presenting the arriving request's data-array address
in its capture cycle (the array reads every way per address; the way is
selected after the tag compare) and depositing the hit from the port in the
classify cycle. Requests that cannot take that path -- a write hit, a read
behind a pending write, a read whose lead lost the port to the commit's
read cursor -- fall back to the serve record, which since TASK-003 led its
own address in the classify cycle and fired a cycle later. The first cut
gave the arriving request's lead priority over the occupant's: in a stream
the port was always wanted by the next request, so an occupant that needed
the fallback lost its lead too, re-presented its address from the record a
cycle later, and because the record is one deep the classify held behind
it. On the board the hit floor read 2 and the pure-read resident row
matched HPDcache; the mixed read/write resident rows at depth 4 and 16 went
from 1.01 to 1.76 cycles per transaction. The depth-1 rows, which are what
the task was about, all improved.

**The fix.** The fast path's resource grab yields whenever the occupant
might need the fallback: its own lead did not land, the array was written
at that edge, a record is pending, the commit deposits this cycle. All of
those are registers or commit state, so the yield costs the address mux
nothing it did not already carry. After a write the stream runs the old
path at the old rate until a bubble lets a lead land again; a pure read
stream takes the fast path on every hit.

**The rule.** When a fast path is added beside an existing path, list what
the existing path consumes and in which cycle, and make the fast path's
grab conditional on the slow path not needing it -- not on the fast path's
own chance of success. A speculative grab that is "harmless when it fails"
is harmless only to the request that made it.

**And the measurement.** The property the task names (the hit floor, the
depth-1 rows) is the one the first look confirms. The rows that exercise
the fallback -- mixed traffic at the depths where the pipe is full -- are
where a priority inversion shows, and they are in the same sweep. Read the
whole table against the previous bin before calling a step done; bin 5a's
regression was two rows away from the headline.

Related: [[enforce-the-contract-at-the-hazard]] (the same block, the
opposite lesson: a gate that was too early), [[checks-encode-events-not-cycles]].
