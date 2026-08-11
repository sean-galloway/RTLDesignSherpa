<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# common — Open (accepted, not started)

---

## COMMON-007 — Additional arbiter types
**Status:** open — ONLY the hierarchical (grouped two-level) item remains,
deferred pending a consumer. Deferral RE-CONFIRMED by Sean 2026-08-11 after
a full elaboration of the design space (fairness semantics across unequal
group sizes, per-level discipline pairing, two-level ACK plumbing, latency)
— every open decision needs a named consumer to settle it. DRR slice DONE 2026-08-09; token bucket DONE
2026-08-10 (both with full DV, see progress). Shaped 2026-08-09
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
- DV follow-up DONE 2026-08-10: RDS-DV#65 filed and closed by RDS-DV
  2e3f4ff — DeficitRoundRobinArbiterMonitor + ArbiterCompliance 'drr' mode
  (windowed served-cost shares vs quanta, zero-quantum-grant errors, NO RR
  mask replay). Three false-positive classes were found and fixed by
  running it against the real DUT before shipping: completion-cycle cost
  attribution (needs the arbitration-cycle sample), windows straddling
  participation changes (now require a stable requester set and normalize
  over requesters' quanta), and fixed-size windows reading a lumpy
  high-cost/low-quantum client as deviation (window now scales with client
  count). The main-repo TB uses the framework monitor and ASSERTS on its
  compliance verdict; the cycle-exact deficit mirror stays TB-side by
  design (it knows the driver's cost intent). GATE/FUNC/FULL green,
  RR/WRR sibling tests unaffected.

**Progress 2026-08-10 — token bucket slice DONE:**
- `rtl/common/arbiter_token_bucket.sv`: free-standing per-client shaper
  (external refill_tick pairs with counter_freq_invariant; packed runtime
  rate/cap; cap 0 = UNSHAPED fail-open; overspend-proof gate nets out the
  in-flight spend - the registered-decision lesson again; no config FSM,
  and the cap clamp is a per-cycle INVARIANT, not a refill-time bound - a
  lowered cap bites immediately, found when clients carried burst across a
  cap change). Filelist registered (common 48/48), doc page, book index +
  CLAUDE matrix + technique-index rows. GATE/FUNC/FULL green, both ACK
  modes, 4-16 clients, never-overspend ledger asserted per completion.
- Two TB lessons paid: sample AFTER a settle delay (reading combinational
  outputs in the same delta as RisingEdge returns pre-edge values - the
  "overspend" was the TB arbitrating on a stale gate), and scenario configs
  must respect field widths (cap 8 in a 3-bit field wraps to 0 = bypass).
- Naming: w_client_* prefixes per [[signal-prefixes]] in both new arbiter
  modules (the WRR's unprefixed client_weight precedent was NOT followed).
