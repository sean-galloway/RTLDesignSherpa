# gatling-rv32i — Task Index

Tetrad compute engine (barrel RV32I + Xcell), one engine per tetrad,
4 contexts = 4 cells. PRD: [projects/components/riscv-ip/gatling-rv32i/PRD.md](../../../../../../projects/components/riscv-ip/gatling-rv32i/PRD.md)

## Open

| Item | Summary |
|---|---|
| [ISSUE-001](issue/open/ISSUE-001.md) | build-tetrad answered one UART read with ERR on its first run; nothing on the path returns a non-OKAY response; not reproduced since |

## Deferred

| Task | Summary |
|---|---|
| [TASK-003](task/deferred/TASK-003.md) | Split the X stage to clock above 100 MHz; owner 2026-10-21: 100 MHz is good enough. Un-defers when a consumer needs more |

## Closed

| Task | Summary |
|---|---|
| [TASK-005](task/closed/TASK-005.md) | Interlock bounded liveness (prove_live / prove_isolate PASS at depth 100) and the tetrad on the Nexys A7 (bf16, 4.6875 MHz, N = 96 and 384 golden-identical) |
| [TASK-002](task/closed/TASK-002.md) | Gatling RTL bring-up: barrel, Xcell (custom-0) and the tetrad; the hand-assembled tetrad program runs in DV on the real cell blocks against alu-infer's golden |
| [TASK-004](task/closed/TASK-004.md) | FPGA rework: the per-context PC file in distributed RAM (common-rv32i ISSUE-001 row 4); 1,308 -> 1,200 LUT, 894 -> 772 FF, WNS +0.190..+0.470 -> +0.424..+0.660 over 3 placer directives |
| [TASK-001](task/closed/TASK-001.md) | Tetrad compute FSM: kestrel-evaluation answered by gatling; PRD §7 decisions all settled (2026-10-21: implicit context, separate program regions, context-lock) |
