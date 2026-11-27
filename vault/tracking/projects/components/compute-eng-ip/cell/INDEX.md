# cell — Task Index

The lowest compute module: alu-infer ALU + delta node + config registers +
ALU registers (A-D, T) + data-in memory + data-out memory + exec FSM.
Home: `projects/components/compute-eng-ip/cell/` (PRD v0.5, MAS v0.12).
Slice 1 (fill path) built; slices 2-3 specified.

## Open

| Task | Summary |
|---|---|
| [TASK-001](task/open/TASK-001.md) | Slice 2: cell_credit + cell_packetizer + strap counter |
| [TASK-002](task/open/TASK-002.md) | Slice 3: cell_exec_fsm + ALU hookup + MonBus observer |
| [TASK-003](task/open/TASK-003.md) | Build cell_mem_in / cell_mem_out as distributed RAM (1,062 FF each today: arrays written in the reset block) |
| [BUG-001](bug/open/BUG-001.md) | test_cell has no `full` level (KeyError at module load) |

## Closed

(none yet)
