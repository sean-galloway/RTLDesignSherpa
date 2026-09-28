<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# RLB — tasks

**Next ID: TASK-018** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 3 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 15 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-000** — reserved template; copy the file, do not file against it.
- **TASK-017** — an interrupt-line BFM (`TBClasses.irq`) and per-block routing coverage for the rlb_top fabric; closes the gap TASK-015 left where only GPIO was proven end to end.
- **TASK-016** — RLB placement pass: 7 loose markdown files (status/roadmap/audit beside the RTL, a Makefile README beside the tests)


## Closed

- **TASK-001** — MAS/RTL quality review (9 blocks) via Kimi
- **TASK-002** — Fix wrong-map MAS register documentation (5 blocks)
- **TASK-003** — Fix remaining MAS register documentation (4 blocks)
- **TASK-004** — Triage & fix the RTL bugs found by the MAS/RTL review
- **TASK-005** — Clean up rtc wavedrom README third register-map copy
- **TASK-006** — scrub the tests for completeness (retro legacy blocks)
- **TASK-007** — all RDL lives in an rdl area, as it does elsewhere
- **TASK-008** — IOAPIC features deferred past the #48 fix
- **TASK-009** — PM_ACPI features deferred past the #54 fix
- **TASK-010** — RTC leftovers after the #56 fix
- **TASK-011** — SMBus features deferred past the #58 fix
- **TASK-012** — UART 16550 features deferred past the #60 fix
- **TASK-013** — the 800-line core cap is honored in the breach
- **TASK-014** — pit_regmap.py regenerated to match its RDL
- **TASK-015** — rlb_top interrupt fabric: block IRQs reach both 8259s and the IOAPIC internally, plus the aggregated `rlb_irq_out`; GPIO proven end to end, closed 2026-09-28.
