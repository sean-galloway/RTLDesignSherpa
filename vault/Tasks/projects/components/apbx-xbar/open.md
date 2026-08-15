<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# apbx-xbar — Open

---

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
