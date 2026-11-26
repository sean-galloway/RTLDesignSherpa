# Rung Three

## The ladder

| Rung | Core | ISA | Shape | What it teaches |
|------|------|-----|-------|-----------------|
| 1 | kestrel | RV32I | Single cycle | The datapath and the control truth table |
| 2 | merlin | RV32I | Five-stage pipeline | Hazards, forwarding, the cost of a taken branch |
| 3 | peregrine | RV32IM | Pipeline extended | Speculation, precise traps, a structural hazard, caches |
| 4 | gyrfalcon | RV32IMA | Out of order | Rename, a reorder buffer, the scoreboard peregrine declined |

: The falcon ladder (falcon-suite design, rungs 1 to 4)

## Why these four additions belong together

The four additions share one mechanism: a way to throw work away. A
mispredict discards the two instructions fetched behind a branch. A trap
discards everything younger than the trapping instruction. An M
instruction held in EX turns the stages behind it into bubbles. A cache
miss freezes the whole machine. peregrine has exactly two redirect
points (EX for a mispredict, MEM for a trap, `mret` or `fence.i`) and one
global hold (`mem_wait`), and every lesson in this book is a rule about
how those three interact.

## What peregrine hands on

gyrfalcon's baseline ISA is peregrine's RV32IM, so every peregrine test
battery carries over unchanged. gyrfalcon reuses the predictor, the trap
machinery, the caches and the AXI fabric (PRD §1). Chapter 7 says what
changes.
