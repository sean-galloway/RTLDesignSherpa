<!-- Managed by the `tasks` convention: see /vault/tracking/INDEX.md. -->

# projects/components/compute-eng-ip/alu-infer — tasks

**Next ID: TASK-008** — never recycle a number, even when its item closed.

Planned work we have decided to do: a feature, a refactor, a migration, a cleanup. It starts from intent, not from a failure.

Each item is **its own file**, `<ID>.md`, inside the directory for its state.
Moving an item between states is `git mv`, so an item is in exactly one state
by construction rather than by discipline.

| State | Count | What |
|---|---|---|
| [open/](open/) | 7 | accepted, not started |
| [active/](active/) | 0 | in progress right now |
| [closed/](closed/) | 0 | done (kept for history) |
| [dropped/](dropped/) | 0 | ended without completing |
| [deferred/](deferred/) | 0 | parked pending a named condition |

## Open

- **TASK-001** — line-reduce row: sum/max tree over a span of lines into the fp32 accumulator (unlocks softmax/layernorm/pooling); owner ruling 2026-10-19, PRD §3 roadmap
- **TASK-002** — PWL/LUT activation row: 256-entry LUT + linear interpolation for sigmoid/tanh/gelu/exp; exp + reciprocal-multiply covers softmax's divide; owner ruling 2026-10-19, PRD §3 roadmap
- **TASK-003** — const/bias row: emit the immediate register as a result line so programs build bias lines without memory traffic; owner ruling 2026-10-19, PRD §3 roadmap
- **TASK-004** — int8 x4-lane element width via func_sel[8:7] (open item M6): same MAC fabric, 4 MACs/clk; owner ruling 2026-10-19, PRD §3 format roadmap
- **TASK-005** — fp32 single-lane element width via func_sel[8:7] (open item M6): general vector engine; owner ruling 2026-10-19, PRD §3 format roadmap
- **TASK-006** — tag/same-tag alignment in RTL: 8-bit tag + tag FIFO + align gate replace the alu_infer_pipe timer mailbox when rows gain uneven pipeline depths (ratified 2026-10-17, not yet in RTL)
- **TASK-007** — close the M1-M8 numeric-policy open items at FPGA bring-up (NaN/inf semantics, exception flags, FTZ policy, threshold_imm encoding, element-width field, ROW_LATENCY table)

## Active

## Closed
