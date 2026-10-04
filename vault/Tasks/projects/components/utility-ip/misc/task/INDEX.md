<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/components/utility-ip/misc — tasks

**Next ID: TASK-006** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 1 | in progress right now |
| [closed/](closed/) | 4 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

## Active

- **TASK-003** — axis4_intf_observer instantiates axis_monitor_lite instead of its private per-port tap; RTL done 2026-10-04 (c35c8304b), suite 12/12 green, board packet-class matrix pending the ecc-ip lane's harness


## Closed

- **TASK-005** — single-port arbiter padding: width guards landed in all
  three arbiters (CLIENTS=1 elaborates), observer padding deleted, suite
  12/12 green, arbiter formal PASS (closed 2026-10-04 as measurement-
  disproven scope: the "wasted grant" was the documented single-requester
  ACK dead cycle — removing it fails the monbus formal proof; OUT_DEPTH 16
  stays for the err-FIFO burst)
- **TASK-001** — all RDL lives in the rdl directory -- CLOSED 2026-09-29: obs/tally/dma_address_gen RDL under rdl/<block>/; 9 referrers updated; check_rdl_regen PASS from the new paths
- **TASK-004** — misc placement pass: FUTURE.md is a work list at the component root -- CLOSED 2026-09-29: FUTURE.md deleted; its TASK-101 pointer moved to the CLAUDE.md module table
- **TASK-002** — scrub the tests for completeness (misc)
