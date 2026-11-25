# ISSUE-008: a rare one-cycle draw survives refresh alignment -- one board row in 263 differed by a cycle at the same REF_ALIGN offset

> Source: memory-controllers MC-022 board check, 2026-11-25
> (`char_results/board_mc022_pick_cone_sku100_2026-11-25.md`, section 5).

**Priority:** P3 -- one cycle on one row; no conclusion so far depends on it,
but MC-025's promise is cycle-exact A/Bs, and an unexplained draw is a source
of noise that will be mistaken for a microarchitectural difference.
**Status:** open 2026-11-25
**Owner:** TBD

## The observation

At `TEST_REF_ALIGN=0` on the granite sys100 SKU, `every` / `defaults` /
`row_major_bl4` wrote in 269,754 MC cycles on one run and 269,753 on every
other run: MC-025's two (build B of its RTL), MC-022's two repeats of
`defaults` and one more on MC-025's bitstream. Every other row of those runs
matched to the cycle (263 rows compared in all, 0 mismatched beats).

## What it is not

- The MC-022 change: its bitstream read 269,753 on both repeats, and the
  change is proven exact against the golden copy.
- A bitstream difference: MC-025's bitstream read 269,753 again.

## What to find

Some state that outlives the tREFI reload and is not reset at a launch: a
free-running counter (page-policy idle timers, direction counters), a
clock-domain crossing whose landing cycle varies with the host's timing, or
DRAM-side state left by the previous cell. First step: repeat the full
`every` at offset 0 several times on one bitstream to measure the rate and
see whether the drawn rows are always the same; then probe the row that
draws.
