<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# delta — tasks

**Next ID: DELTA-011** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a
cleanup. It starts from intent, not from a failure.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 3 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open
- **DELTA-010** — `delta_mesh_cell` advertises its cell's input-buffer credits
  from a parameter at reset (TILE_SPEC 11.10; pairs with rapids TASK-027)

## Closed
- **DELTA-009** — systolic package: torus wrap links, dateline rule, route
  lookahead, source-route override, and speculative VA+SA; speculation parity
  failure root-caused and fixed (closed 2026-10-15)

- **DELTA-002** — delta HAS + MAS books authored from scratch (v1.0, house naming + house-style diagrams; 2026-10-12)

- **DELTA-001** — axis flavor richness: optional TSTRB + AMBA 5
  TWAKEUP/TPARITY generator options (default off; default output byte-identical;
  TPARITY later replaced by the IHI 0051B check signals under GitHub #102);
  rich example `rtl_test/delta_axis_flat_2x4_strb_amba5.sv` lints clean
  (closed 2026-10-12)
