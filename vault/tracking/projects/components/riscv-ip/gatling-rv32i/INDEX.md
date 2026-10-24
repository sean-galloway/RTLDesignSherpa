# gatling-rv32i — Task Index

Tetrad compute engine (barrel RV32I + Xcell), one engine per tetrad,
4 contexts = 4 cells. PRD: [projects/components/riscv-ip/gatling-rv32i/PRD.md](../../../../../../projects/components/riscv-ip/gatling-rv32i/PRD.md)

## Open

| Task | Summary |
|---|---|
| [TASK-002](task/open/TASK-002.md) | Gatling RTL bring-up: barrel model chapter, RTL, HAS/MAS (blocks tile milestone M1) |

## Deferred

| Task | Summary |
|---|---|
| [TASK-003](task/deferred/TASK-003.md) | Split the X stage to clock above 100 MHz; owner 2026-10-21: 100 MHz is good enough. Un-defers when a consumer needs more |

## Closed

| Task | Summary |
|---|---|
| [TASK-001](task/closed/TASK-001.md) | Tetrad compute FSM: kestrel-evaluation answered by gatling; PRD §7 decisions all settled (2026-10-21: implicit context, separate program regions, context-lock) |
