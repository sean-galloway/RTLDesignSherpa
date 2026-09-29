<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# RLB — tasks

**Next ID: TASK-020** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 0 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 19 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open



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
- **TASK-017** — an interrupt-line BFM (`TBClasses.irq`) and per-block routing coverage for the rlb_top fabric; all six blocks proven to their PIC input and their IOAPIC pin (vectors 0x40/0x44/0x48/0x49/0x4A/0x4B), plus a coincident-assert case, closed 2026-09-28.
- **TASK-016** — RLB placement pass: the 7 loose markdown files rehomed (status/roadmap/audit to this lane, two reader-facing pages to `docs/`), the Makefile README slimmed to a pointer at `make help`, and a generated pm_acpi orphan deleted; closed 2026-09-28.
- **TASK-018** — per-IR-line PIC assertions: each of the six blocks proven to its OWN IR line (`w_fabric_irq[irq]` plus an exact master set including the cascade bit), and three coincident sources spanning both PICs (UART on master IR4 with GPIO+PM under the cascade); closed 2026-09-28.
- **TASK-019** — the RLB follow-up batch, all five resolved: the per-IR-line check promoted to `func` (0 -> 1 logged line); a source/line cross-check so the source-name and per-IR-line halves cannot pass while disagreeing; a four-coincident test spanning both PICs (`fabric [4,9,10,11]`, `master [2,4]`); 8 MB of committed generated docs deleted and RLB's divergence recorded as deliberate; and all eleven beside-code READMEs justified in place rather than converted. Closed 2026-09-29.
