<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# delta — tasks

**Next ID: DELTA-002** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a
cleanup. It starts from intent, not from a failure.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 1 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Closed

- **DELTA-001** — axis flavor richness: optional TSTRB + AMBA 5
  TWAKEUP/TPARITY generator options (default off; default output byte-identical);
  rich example `rtl_test/delta_axis_flat_2x4_strb_amba5.sv` lints clean
  (closed 2026-10-12)
