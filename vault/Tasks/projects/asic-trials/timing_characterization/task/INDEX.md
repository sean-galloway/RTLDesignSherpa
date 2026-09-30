<!-- Managed by the `tasks` convention: see /vault/Tasks/INDEX.md. -->

# projects/asic-trials/timing_characterization — tasks

**Next ID: TASK-006** — never recycle a number, even when its item closed.

planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 1 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 4 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-003** — Additional FUBs

## Closed

- **TASK-004** — PDF Generation for Synthesis Guide -- CLOSED 2026-09-29: docs/generate_synthesis_guide_pdf.sh + Timing_Characterization_Synthesis_Guide_v1.0.pdf (20 pp)
- **TASK-002** — Cross-Technology Comparison Reports -- CLOSED 2026-09-29: docs/baseline_results.md generated from Artix-7 + Cyclone V frequency sweeps and CARRY_WIDTH / NAND_LEVELS / MULT_TYPE sweeps
- **TASK-005** — timing_characterization placement pass: 3 loose how-to guides -- CLOSED 2026-09-29: ASAP7 flow how-to -> new handbook asic/ area; README_FPGA (paper source) and SYNTHESIS_GUIDE (tool mechanics) stay
- **TASK-001** — Parameter Sweep Automation Scripts -- CLOSED 2026-09-29: Quartus sweep (fpga/quartus) + example config built and run on Cyclone V; parser fixed for both tools
