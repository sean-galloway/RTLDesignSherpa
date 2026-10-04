<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/utility-ip/misc — tasks

**Next ID: TASK-006** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 2 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 3 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-004** — single-port observers pad monbus_arbiter to 2 clients; the
  idle padding client wastes every other grant (measured monbus_ready 1/1
  toggle), and burst back-pressure from the 64-record egress err FIFO then
  drops tap events at the core's default OUT_DEPTH 4/8 (killed Channel on
  all_classes FULL). Fix the grant waste + CLIENTS=1 width guard; observer
  workaround (OUT_DEPTH 16) rides it out meanwhile

- **TASK-003** — axis4_intf_observer instantiates axis_monitor_lite instead of its private per-port tap (one implementation of the AXIS event set)


## Closed

- **TASK-001** — all RDL lives in the rdl directory -- CLOSED 2026-09-29: obs/tally/dma_address_gen RDL under rdl/<block>/; 9 referrers updated; check_rdl_regen PASS from the new paths
- **TASK-004** — misc placement pass: FUTURE.md is a work list at the component root -- CLOSED 2026-09-29: FUTURE.md deleted; its TASK-101 pointer moved to the CLAUDE.md module table
- **TASK-002** — scrub the tests for completeness (misc)
