---
title: A "hold, not a stall" that waits on another agent is a wait on the fabric; no grant rule may wait for it
summary: jet v3 deadlocked (pair-rig SEED 27994) because the snoop grant waited for an empty lookup pipe, the pipe occupant was held on the fill-launch register, the launch waited on the fill engine, and the engine's AR waited on a fabric that was itself waiting for this core's snoop response. Every link had a "bounded" argument; the bound assumed the fabric was free. Rule: a stage may hold on a resource whose release depends on another agent only if nothing that agent needs from us waits on the hold.
---

# A hold that waits on the fabric is not bounded

**The chain (jet v3, 2026-11-07).** The pair-rig deadlocked with the fabric in
F_RESP, both cores' ARs valid and not accepted, no AC presented, both control
FSMs idle. The hang dump (now printing both cores' snoop-safe terms) read:

```
core0: lk_valid 1  stall 0  sn_want 1  sn_req 0  sn_safe 0  fill_pend 1  fill_start 1  fill_accept 0  eng_busy 1
fabric: F_RESP  grant_q 1  (snooping core 0, waiting for its CR)
```

Five links, each individually "bounded":

1. the fabric waits for core 0's snoop response before it accepts any AR;
2. core 0 will not grant the snoop while its lookup pipe holds a request
   (`sn_safe_o` had `& ~r_lk_valid`, "bounded: the classify is one cycle plus
   any bounded classify stall");
3. the occupant is a true miss HELD, not stalled, on `!r_fill_pend` -- the
   fill-launch register is busy;
4. the launch register frees when the fill engine accepts, and the engine is
   busy with the previous fill;
5. that fill's AR is the one the fabric will not accept (link 1).

The "bounded classify stall" in link 2 was true for every STALL reason (they
resolve on local events: a commit retiring, a pend draining, the WB freeing).
It was false for the HOLD cases, which the classify does not even report as
stalls: fill-launch register busy, upgrade pipe busy, pend room. Those wait on
the fill engine, which waits on the fabric, which waits on us.

**Rule.** Walk every "hold" in a stage and name the agent that releases it.
If the release depends on another agent (the fabric, a peer core, memory),
then no grant that agent needs from this block may be conditioned on the hold
clearing. Either the grant rule must not look at the held stage, or the stage
must be able to make progress without the other agent.

**The fix was the grant rule, not the hold.** The empty-pipe term was
unnecessary: a captured-not-classified request still runs against post-snoop
state because the classify holds in the grant cycle (`w_cls_advance &
~w_sn_gnt`) and through the service (`r_sn_state != SN_IDLE`), a service tag
write to the request's set marks the snapshot dirty and replays the read
([[decision-stage-reads-the-snapshot]]), and the MSHR CAM, WB CAM, claim
count and victim way are live lookups. Dropping `~r_lk_valid` and adding the
grant-cycle hold cleared the seed (16,076 checks, 0 mismatches).

**How it was found.** Three runs of the same seed with items 2 and 3 reverted
all hung at the same cycle (so not the FPGA rework); then the hang dump was
extended from "which FSM is where" to the actual terms of the grant rule. The
first dump said only "fabric waiting, cores idle"; the second said which bit
of `sn_safe_o` was 0 and why the occupant could not move. Print the terms of
the rule, not the state of the machine.

**The same wait, one layer up (jet BUG-004, 2026-11-11).** Four days
after the fix above, the first PIPELINED stimulus on the Genesys2 pair rig
(the cycle injector of cache-ip common-ip TASK-002, eight requests in
flight per cache) deadlocked the same rig with the fabric in F_AC: both
cores' ARs held, no AC presented, both lookups live and held on their
fill-launch registers. `jet_pair_fabric`'s safe-peer wait consumed the very
occupancy bit `jet_control` had stopped waiting on -- exported as
`lkup_live` for the fabric's registered-peer-state window -- and waited for
it to clear before presenting the snoop. Same five links, with the grant
rule now in the fabric instead of the core. Two lessons:

- **A signal removed from one grant rule must be chased to every consumer.**
  The occupancy bit left `jet_control`'s rule but was still exported by
  name; the fabric's rule imported it with the same "bounded" belief. When
  a term is struck from a rule for this reason, grep the signal and audit
  each rule that reads it against the same question (who releases it?).
- **A liveness argument is only as good as the stimulus that can reach the
  posture.** Blocking injectors keep one request per cache in flight and
  can never park a miss behind a held launch; the rig's random soak
  pipelined bursts of at most three with 30 % probability and did not
  reach it in 2,000 transactions. The deadlock needed sustained depth at
  BOTH caches at once. Any interface that admits N in flight needs a
  directed scenario that sustains N (pair-rig scenario (i),
  `DeepPipelinedMisses`, eight back-to-back true misses per CPU) in the
  GATE level, not only a randomized soak.

The fix was again the grant rule: the fabric's pending bypass ("the peer
has a request I hold, so it is waiting on me") no longer demands an idle
peer lookup or an amber miss pseudo-state that jet reports only as a
one-cycle event. jet-mesi-l1 BUG-004 has the dump and the soundness
argument.

Related: [[decision-stage-reads-the-snapshot]], [[valid-ready-contracts]],
[[never-dismiss-failures-as-flaky]] (one seed in sixty, deterministic,
pre-existing).
