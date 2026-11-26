# The Next Rung: gyrfalcon

## What carries over

gyrfalcon, rung 4, is the out-of-order capstone (falcon-suite design).
Its baseline ISA is peregrine's RV32IM exactly, so every peregrine test
battery carries over unchanged, and it reuses the predictor, the trap
machinery, the caches and the AXI fabric (PRD §1).

## What changes

| peregrine | gyrfalcon |
|-----------|-----------|
| An M instruction holds EX; nothing passes it | A scoreboard and reservation stations: independent work passes a busy unit |
| In-order completion, so RVFI reports results in order for free | Out-of-order completion; a reorder buffer retires in order, and RVFI reports at retire |
| Precise traps by committing at MEM | Precise traps by retiring from the reorder buffer in order |
| Two redirect points, one global hold | Recovery from any point in a speculative window |

: From rung 3 to rung 4

The thing peregrine declined in Chapter 4, letting work pass a busy
multiply, is the first thing gyrfalcon does. The reason peregrine
declined it, that results must be reported in program order, is the
reason gyrfalcon needs a reorder buffer.
