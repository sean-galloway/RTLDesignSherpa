<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# apbx-xbar — Open

---

## APBX-002 — Formal coverage for the APB4/APB5 version gating
**Status:** open 2026-08-14 — split out of APBX-001 at close

The SymbiYosys proofs under `formal/apbx_xbar/` were updated for the
sideband ports (harnesses tie the inputs, leave the outputs open) and
still pass, but they only ever run the **default all-APB4
configuration**. Nothing formal constrains the thing APBX-001 actually
added.

Worth proving, and cheap because the masks are parameters on the thin
core — a harness can be instantiated per configuration:

- with `MST_APB5[m]=0`, `s_apb_pauser`/`pwuser` are `'0` on every slave
  regardless of what master *m* drives (an APB4 master cannot leak);
- with `SLV_APB5[s]=0`, slave *s*'s sideband outputs are `'0` for every
  granted master (an APB4 slave is never driven);
- with both set, the sideband equals the granted master's within the
  granted window.

Simulation already checks all three, so this is about proving them
exhaustively rather than for the sampled stimulus.

## APBX-003 — APB5 parity across the fabric
**Status:** open 2026-08-14 — split out of APBX-001 at close

APB5's parity feature (`PSELPARITY` and the rest) is not carried. The
generated variants instantiate their boundary IP with `ENABLE_PARITY=0`
and tie the parity pins off; wakeup and the user buses are the sideband
that is supported.

This is not just wiring more pins. Parity is a protection-domain
question — whether the crossbar re-generates parity at each boundary or
passes it through end-to-end changes what a fault in the fabric itself
looks like, and the answer should be written down before RTL. Decide
that first, then implement.
