<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# apbx-xbar — Open

---

## APBX-003 — APB5 parity across the fabric
**Status:** open 2026-08-14; protection-domain decision made 2026-08-15,
ready to implement

APB5's parity feature is not carried. The generated variants instantiate
their boundary IP with `ENABLE_PARITY=0` and tie the parity pins off;
wakeup and the user buses are the sideband that is supported.

### Decision (owner, 2026-08-15)

**A mixed pairing ignores parity.** An APB5 port talking to an APB4 port
has parity ignored, exactly as the other sideband is gated — the same
`MST_APB5`/`SLV_APB5` masks decide it, and no new policy knob is needed.
This falls out of the model already proven in [[APBX-002]]: features
exist only on paths that are APB5 at both ends.

### What that leaves, and what the RTL already forces

The remaining question was APB5→APB5, and it turns out **not to be a
free choice — the two families answer it differently, because their
architectures differ:**

- **Generated variants: check-and-regenerate, forced.** `apb5_slave`
  *checks* parity and raises `parity_error_wdata` / `parity_error_ctrl`;
  the parity bits do **not** cross into the cmd/rsp interface, so they
  physically terminate at the boundary and `apb5_master` computes fresh
  ones on the far side. End-to-end pass-through is not available here
  without changing the boundary IP's interface. Consequence to accept
  and document: the cmd/rsp fabric between check and regenerate is
  outside the protected domain, so corruption there arrives with valid
  parity.
- **Thin core: pass-through, free.** It is a combinational mux that does
  not modify the payload — the address and write data reach the slave
  unaltered — so the master's parity is still correct at the far end.
  Parity bits can ride the same grant/demux muxes as the other
  sideband, giving true end-to-end coverage for zero extra logic and
  catching corruption *inside* the mux, which the variants cannot.

### The one thing still undecided

`parity_error_wdata` / `parity_error_ctrl` on the generated variants
need a destination. A check whose result goes nowhere is not
protection. Options: bring them out as a per-port error vector, fold
them into `PSLVERR`, or emit them on the monbus like the AXI monitors
do. **Recommendation: a per-port error output**, since folding into
`PSLVERR` would make a fabric fault indistinguishable from a slave's
own error response, which is precisely the distinction parity exists to
draw.

### Implementation shape

Thin core: parity ports gated by the existing masks, plus a formal
property in the [[APBX-002]] harness (an APB4 port never sees parity;
an APB5→APB5 path passes it unaltered). Generated variants: set
`ENABLE_PARITY=1` on APB5 boundary IP and route the error flags.
Both are the same shape as the sideband work already landed.
