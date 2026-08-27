<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# apbx-xbar — Dropped (ended without completing)

---

## APBX-006 — apbx_xbar_thin presents NO setup phase downstream (PSEL and PENABLE assert together)
**Status:** open 2026-08-27 (found by qc round_9, measured)
**Priority:** P1 — APB protocol violation; a compliant slave may never latch PADDR
**Owner:** TBD — needs a design decision, see options

AMBA APB requires one SETUP cycle (PSEL high, PENABLE low) before ACCESS.
`apbx_xbar_thin` gives downstream slaves **zero**.

**Mechanism.** The downstream strobes are grant-gated passthroughs of the
master's own strobes:

```systemverilog
s_apb_psel[s]    = arb_gnt_valid[s] ? m_apb_psel[mst_id]    : 1'b0;
s_apb_penable[s] = arb_gnt_valid[s] ? m_apb_penable[mst_id] : 1'b0;
```

`master_sel` is combinational, so the arbiter sees the request during the
master's SETUP cycle -- but `arbiter_round_robin_weighted`'s grant is
REGISTERED (its own header: "request at edge N -> grant_valid at edge
N+1"). By the time the grant opens the gate, the master is already in
ACCESS with PENABLE high, so PSEL and PENABLE rise together at the slave.

**Measured**, not inferred: a probe on the `M=2,S=2` mixed configuration
counted setup-phase cycles before each downstream ACCESS as
`[0, 0, 0, 0, 0, 0]` across three transfers (6 slave-side accesses).

**Why it has not bitten.** This repo's own `apb4_slave`/`apb5_slave`
capture on the rising edge of PENABLE, so they tolerate it, and the
existing thin tests only ever drive those. A third-party slave that
latches PADDR/PWRITE during `(PSEL && !PENABLE)` would never latch them.
HAS ch04_interfaces/02_slave_side.md documents the opposite ("PENABLE:
low during setup phase"), so the docs promise compliance the RTL does not
deliver.

**Options (needs a decision):**
1. Delay the downstream PENABLE by one cycle after the grant opens --
   smallest change, costs a cycle per transfer.
2. Hold the request into the arbiter and delay PSEL passthrough so the
   master's own SETUP cycle lands after the grant -- no added latency,
   more control logic.
3. Use a combinational grant path for the strobes -- fastest, but the
   weighted arbiter's registered grant is load-bearing for its credit
   accounting.

Any of these re-opens `formal/apbx_xbar/apbx_xbar_thin{,_mixed}`, which
must be re-proven. That is why this is filed rather than fixed in the
qc pass: it is a design change to a formally-verified module, not a doc
correction.

**Related:** [[TASK-071]] (amba) -- `apb4_master`/`apb5_master` drive a
TWO-cycle setup phase out of IDLE, the opposite deviation, in the
generated variants' boundary IP.

**DROPPED 2026-08-27: `apbx_xbar_thin` is retired.** The protocol
deviation above is real and was measured, but the module it affects is
no longer a supported part of the family, so there is nothing to fix.
Nothing instantiated it outside its own two formal harnesses
(`formal/apbx_xbar/apbx_xbar_thin{,_mixed}`) — `retro_legacy_blocks`
uses its own generated `apbx_xbar_rlb_1to10`, not thin.

**Does NOT retire with it:** [[TASK-071]] (amba) — the TWO-cycle setup
phase in `apb4_master`/`apb5_master`. That is the boundary IP inside the
GENERATED variants, and it is shared with the converters and the
bridges, so it stands on its own.

---

