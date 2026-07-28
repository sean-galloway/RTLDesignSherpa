<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. Move a task between pages by cutting its block, do not copy. -->

# bridge — open

## BRIDGE-001 — Generator emits NUM_SLAVES as a body localparam used in the port list
**Status:** open 2026-07-28
**Priority:** P1 — blocks clean commits of any regenerated bridge
**Owner:** TBD

The bridge generator emits `NUM_SLAVES` as a **body** localparam at line ~719
of the generated xbars while using it in the module **port list** (line ~16).
Verilator elaborates this; iverilog and other strict front ends reject it, and
the repo's pre-commit declaration-order hook BLOCKS the commit. Seen on both
generated xbars:

- `.../generated/bridge_stream_mon_axil/bridge_stream_mon_axil_xbar.sv`
- `.../generated/bridge_stream_mon_axil_mon/bridge_stream_mon_axil_mon_xbar.sv`

The hook's own guidance is the fix shape: move `NUM_SLAVES` into the parameter
port list (`module M #(..., parameter int NUM_SLAVES = ...)`), where it is
elaborated in order, and drop the body declaration.

**How it surfaced:** the stream-mon AW/W decoupling WIP (commit `c529ba49`)
regenerated the bridges and hit the hook; it was committed with `--no-verify`
to transfer between machines, so the debt is live on main.

**Rules that apply:**

- **Fix the GENERATOR, never the generated files** — hand edits regenerate away.
- **Rule #0 (CLAUDE.md): full regeneration.** Delete ALL generated bridge
  outputs and regenerate everything from scratch; partial regeneration causes
  silent version-mismatch failures. Then run the full bridge DV suite, not
  just the configs that changed.
- **Sweep for the class, not the instance** — check the other generated
  modules (wrappers, host/monbus/descriptor adapters) for the same
  body-localparam-in-port-list pattern, and any other parameters emitted the
  same way.

**Done looks like:** generator fixed, all bridge configs regenerated, bridge
DV green, and `git commit` of a regenerated bridge passes the pre-commit hook
with no `--no-verify`.
