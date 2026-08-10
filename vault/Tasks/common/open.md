<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# common — Open (accepted, not started)

---


## COMMON-007 — Additional arbiter types
**Status:** open — deferred pending user requests, P3. Shaped 2026-08-09
against the current arbiter lineup (question from Sean: are these modes of
the existing WRR?).

Token bucket, deficit round-robin, hierarchical arbitration. Current arbiters
cover ~95% of use cases and complex arbiters tend to be application-specific.

**How each maps onto today's `arbiter_round_robin_weighted`** (credit-based
QoS, runtime weights, global replenishment, ACK protocol):

- **Deficit round-robin = a MODE of the current WRR**, not a new module. The
  WRR's credit counters already implement DRR for equal-cost requests
  (weight = grants per replenish round). True DRR adds a per-client request
  COST input and spends cost instead of 1, carrying the remainder as
  deficit. Extension to the existing module when a variable-cost consumer
  (packet/burst arbitration) appears.
- **Token bucket = a standalone request-shaper, NOT a WRR mode.** Rate
  shaping, not fairness: per-client token counters gating `request` upstream
  of ANY arbiter. New small block (`arbiter_token_filter` or similar),
  composes with RR/WRR unchanged.
- **Hierarchical = pure composition.** Group arbiter over per-group
  arbiters — a wrapper instantiating existing modules (the monbus arbiters
  are the in-repo composition precedent). No new arbitration logic.

Whoever picks this up: the arbiter compliance model in RDS-DV replays every
grant — extend it alongside (a DRR mode changes the expected-grant math),
and remember randomized traffic does not prove fairness
([[rds-dv-randomization]]); fairness is asserted over a measured window.


