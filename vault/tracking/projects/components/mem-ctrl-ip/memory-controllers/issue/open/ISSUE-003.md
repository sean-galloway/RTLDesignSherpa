# ISSUE-003: close_page pays ~2.5 MC cycles per dependent hop the SKU model does not (board 82-92 MB/s against the model's 104-119)

> Source: memory-controllers MC-018, 2026-11-17. `granite_sku100_close` (every
> column auto-precharging, the board's `close_page` preset) lands 25-30
> percent above the board on the one-bank families (`incremental`, `row_major`,
> `col_major`: model 98-119 MB/s against 78-92) and 30-60 percent above on the
> bank-parallel ones (`col_major_interleaved`, `row_thrash`, `random`: 289-312
> against 180-240), while the same model is within 1 percent of the board on
> every open-page cell of the same families.

**Priority:** P3 -- `close_page` is the experiment's reference preset, not a
shipped point; but the gap is the pipeline's per-hop cost made visible, and it
is the same cost MC-013 saw as the one-slot ceiling before the lane.
**Status:** open 2026-11-17
**Owner:** TBD

## The arithmetic

One 8-byte beat under close_page is ACT -> RD(A) -> (tRTP + tRP) -> ACT: the
model's chain is tRCD 2 + 1 + 3 = 6 MC cycles under tRC 7, so a one-bank
stream moves 8 B per 7 cycles = 114 MB/s, which is the model's cell. The board
moves 8 B per ~9.5 cycles. The extra ~2.5 cycles per beat are what the
decode -> fire pipeline and the next-op hint do not recover when EVERY column
is a dependent hop (the hint lands one hop per fire; a chain of three hops per
beat has two it cannot pre-arm). On open-page streams the hops are one per
burst or per row and the cost is below the model's error bar.

## What settles it

`PERF_PICK_PROBE` on the granite proxy under `close_page` for ~200 cycles of
`incremental`: the cycle each ACT / RDA fires against the cycle its timer
opened. If each hop lands one cycle late, the model gains a `hop_latency`
term (a request's next command no earlier than its last fire + N slots) and
the RTL question is whether the hint can pre-arm the second hop. A recorded
no-action is acceptable: the shipped SKU is open-page.
