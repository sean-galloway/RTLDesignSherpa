<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# common — Active (in progress)

---

## COMMON-007 — Additional arbiter types
**Status:** ACTIVE 2026-08-09 — DRR slice DONE same day (see progress below);
token bucket in implementation next (Sean: "then: Token bucket"); hierarchical
remains deferred. Shaped 2026-08-09
against the current arbiter lineup (question from Sean: are these modes of
the existing WRR?).

Token bucket, deficit round-robin, hierarchical arbitration. Current arbiters
cover ~95% of use cases and complex arbiters tend to be application-specific.

**How each maps onto the existing layered family** (the stack is
`arbiter_priority_encoder` <- `arbiter_round_robin` (rotating mask + ACK)
<- `arbiter_round_robin_weighted` (credit filter feeding the RR) — each
capability is a wrapper layer, per Sean's framing 2026-08-09):

- **Deficit round-robin = a SECOND wrapper beside the WRR**, both around
  `arbiter_round_robin`. The disciplines differ enough to stay separate
  modules sharing the RR core: WRR is weight = consecutive grants per
  global replenish; DRR is quantum-per-round-visit with spend = request
  COST and the remainder carried as deficit. Wanted only when a
  variable-cost consumer (packet/burst arbitration) appears — for
  equal-cost requests the WRR already gives the same shares.
- **Token bucket = a free-standing per-client request shaper**, NOT welded
  to any one arbiter. Same structural position as the WRR's credit mask
  (gates `request` bits) but standalone, so it composes with RR *and* with
  WRR by wiring — shaped rate + weighted share together is the realistic
  QoS combo. A convenience wrapper may follow a proven pairing; the shaper
  itself stays separate.
- **Hierarchical = grouped two-level arbitration** (group arbiter selecting
  among per-group arbiters — hierarchy of CLIENTS, distinct from the
  family's hierarchy of capability layers). Pure composition of existing
  modules; the monbus arbiters are the in-repo composition precedent.

Whoever picks this up: the arbiter compliance model in RDS-DV replays every
grant — extend it alongside (a DRR mode changes the expected-grant math),
and remember randomized traffic does not prove fairness
([[rds-dv-randomization]]); fairness is asserted over a measured window.

**Progress 2026-08-09 — DRR slice DONE:**
- `rtl/common/arbiter_deficit_round_robin.sv` landed as the sibling wrapper
  (quantum shadow FSM, deficit counters, affordability mask into the shared
  RR core), filelist registered (common 48/48), doc page + index/CLAUDE
  matrix rows, technique-index row. GATE/FUNC/FULL all green (2/6/10
  configs, both ACK modes, 4-16 clients), sibling arbiter tests unaffected.
- **Real RTL bug caught during bring-up by the TB's deficit mirror:** the
  grant registers one cycle after arbitration, so debiting the
  completion-cycle req_cost charged a back-to-back client its NEXT frame's
  cost. Fixed with a one-deep cost pipeline (r_cost_arb); lesson recorded
  in [[valid-ready-contracts]] (sideband across a registered decision).
- TB mirror is TB-local (bin/TBClasses/common/arbiter_deficit_round_robin_tb.py);
  promoting it as DeficitRoundRobinArbiterMonitor into RDS-DV
  arbiter_monitor.py is the remaining DV follow-up for this slice. NOTE:
  the framework's compliance analysis logs RR-order "violations" on DRR
  runs (deficit gating legitimately reorders grants) — the promoted monitor
  must carry DRR-aware expected-grant math, not the RR replay.

