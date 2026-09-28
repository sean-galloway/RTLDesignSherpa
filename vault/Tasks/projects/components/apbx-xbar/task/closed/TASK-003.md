# TASK-003: APB5 parity across the fabric

> Migrated 2026-09-27 from `vault/Tasks/projects/components/apbx-xbar/closed.md` as **APBX-003** (tooling TOOL-001). The flat page did not record a lane; this item was placed by hand. Body preserved as written -- only the H1 and this line are new.
**Status:** closed 2026-08-16 — decc2110 (thin core) + 6491f7df (generator)

**Decision (owner, 2026-08-15):** a mixed pairing ignores parity. An
APB5 port talking to an APB4 port has parity ignored, gated by the same
`MST_APB5`/`SLV_APB5` masks as the rest of the sideband. No new policy
knob.

The APB5→APB5 question turned out not to be a free choice — the two
families are forced apart by their own architectures:

- **Thin core: end-to-end pass-through.** It is a combinational mux
  that does not modify the payload, so the requester's parity is still
  correct at the completer. Parity rides the existing grant/demux muxes
  and therefore covers corruption *inside the mux*, which a
  regenerating scheme cannot see — a recomputed bit would be correct by
  construction and would hide exactly that fault. New `ENABLE_PARITY`
  parameter, default 0, so existing builds are bit-identical.
- **Generated variants: check-and-regenerate, forced.** `apb5_slave`
  checks and `apb5_master` regenerates, because the parity bits do not
  cross the cmd/rsp interface the boundary IP deconstructs into. The
  cmd/rsp fabric between them is outside the protected domain and that
  is documented, not hidden.

Because of that unprotected span, the `parity_error_*` flags are
brought out **per port** rather than left dangling — the report is the
only evidence a fault there ever existed. Deliberately not folded into
`PSLVERR`, which would make a fabric fault indistinguishable from the
slave's own error response.

Formal ([[APBX-002]]'s harness) gained two properties: **D** an APB4
port never sees parity in either direction; **E** on an APB5→APB5 path
the parity reaching the slave *equals* what the master drove, which is
what makes the pass-through claim mean anything. prove and cover PASS.

Verified: parity-enabled 2×2 mixed variant lints clean against the real
boundary IP; default generation byte-identical (regenerating the
checked-in tree gives no diff); 6/6 sim suite green.
