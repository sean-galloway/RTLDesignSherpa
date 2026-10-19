# TASK-016: GAS book family created (bridge / apbx-xbar / delta) + apbx HAS/MAS refresh + stale-render purge

**Status:** CLOSED 2026-10-12 (commit in the fabric-gen-ip docs batch). Owner:
"each of these should have a detailed doc for the generators themselves.
Please come up with a name for these. GAS????"
**Priority:** P3

## Name decision

**GAS = Generator Architecture Specification** — slots into the HAS/MAS
family; one per fabric generator. Owner's suggestion adopted as proposed.

## What changed

- New books: `bridge/docs/bridge_gas/`, `apbx-xbar/docs/apbx_xbar_gas/`,
  `delta/docs/delta_gas/` — each covers invocation/CLI, full config schema,
  generation pipeline (real function/module names), emitted artifacts, and an
  extension guide (e.g. adding a protocol = edit
  `config_validator.py` + adapter generators for bridge; DeltaConfig/CLI
  conditionals for delta). v1.0 renders built and sent to Kindle.
- apbx-xbar HAS/MAS refreshed against current RTL/generator/dv, bumped to
  v1.1 (see the batch commit for the mismatch list).
- Stale rendered versions purged across the three components (bridge
  v1.0–v1.9 × PDF/DOCX = 40 files; apbx v1.0 set) — replaces the prior
  accumulate-every-revision practice with current-rev-only.
- `kindle-send` (owner-local tool) extended to accept `*_gas` book dirs;
  titles follow the house convention (`RDS-fabric-gen-ip-<book>`).

## Follow-up (not done)

- kindle-send derives titles correctly but only `*_has|*_mas|*_gas` dirs are
  book-mode eligible — fine for now.
- The pre-existing delta generator/checked-in-RTL drift recorded in
  DELTA-001 still stands (separate decision).
