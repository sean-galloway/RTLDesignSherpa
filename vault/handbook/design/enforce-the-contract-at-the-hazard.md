---
title: Enforce an ordering contract at the hazard, not at the launch upstream of it
summary: jet-prime held every dirty-victim fill LAUNCH until the victim capture ended ("an entry's beats never land before its victim is captured"), ten cycles per miss at depth 1, when the hazard is the array WRITE; holding the beat at the engine's queue head keeps the contract and overlaps the memory round trip with the capture. The tell is a gate on an event that is not the hazard, with a comment arguing why it is sufficient.
---

# Enforce an ordering contract at the hazard, not at the launch upstream of it

**The case (jet-prime TASK-001 step 5, 2026-11-17).** The MAS fill-engine
contract says an entry's fill beats must not land in the data array before
its dirty victim has been captured out of the same way. Steps 2-4 enforced
it at the fill LAUNCH: the plane let a launch reach the engine only when no
capture streamed and the cycle was not a dirty-victim alloc, with a
paragraph in delta 01 arguing why that was enough with several fills in
flight. It was enough. It also put the whole capture -- eight port-B reads
and the sync read's trailing word -- in front of the memory read's round
trip on every dirty-victim miss: on the reference rig a dirty miss took 33
cycles to a clean miss's 23 at depth 1, and on the write-heavy thrash
96 % of the misses were dirty. The first memory beat could not have reached
the array before the capture ended anyway (the rig's first beat lands about
when the capture's last read fires); the hold bought nothing but the wait.

**The fix.** Put the gate where the hazard is: the capture engine exports
its `(set, way)` with `cap_busy`, and the fill engine holds a beat for that
way at its staging-queue head until the capture completes. The launch, the
fabric grant, the snoop and the memory AR all go out in the alloc cycle;
the beats wait only if they actually arrive early. Depth-1 dirty misses
drop to the clean-miss latency. The contract is the same sentence; it is
checked by an assertion at the array write instead of at the launch.

**How to recognise it.** A gate placed on an event that is not the hazard
(a launch, a grant, an accept) because "nothing bad can happen after it
until X completes", plus a paragraph in the docs proving the gate
sufficient. Sufficiency is not the question; cost is. Ask what the hazard
actually is (a write to a location being read, a read of a location being
written, a pointer advance past an un-consumed entry), find the latest
point at which it can be stopped, and gate there. The earlier gate is
usually a leftover from a serial design (amber's blocking FSM did capture
THEN fill, so jet inherited the order as a rule).

**What moves with it.** Every check that encoded the old gate: the tops'
simulation assertions (now "no beat into the captured way"), the core TB's
launch-time check (now at the beat), the formal environment's engine model
(accept unconditionally, hold beats by entry). See
[[checks-encode-events-not-cycles]] for the TB side of the same change.
