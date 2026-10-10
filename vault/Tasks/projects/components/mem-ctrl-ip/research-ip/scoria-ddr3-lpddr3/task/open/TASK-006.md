# TASK-006: two formal/scoria proofs are weak, and the area tally hides it

`formal/scoria` reports 9 blocks passing. Measured across the wrappers there
are **81 live assertions and 6 disabled**, and the disabled ones are not spread
thinly -- they are concentrated in two blocks, which therefore prove much less
than their green status suggests.

| Block | live | disabled | what is NOT proved |
|---|---|---|---|
| `dfi_cdc` | 3 | 4 | the token-accounting edge properties (see below) |
| `wr_data_cam` | 3 | 1 | `a_sram_readback` -- the data-integrity property |
| the other 7 | 76 | 0 | -- |

Updated 2026-10-01: `a_no_extra_staged` is now ENABLED and proved, so the
numbers above are 82 live / 5 disabled. See "Progress" below.

**Priority:** P2. Nothing is known to be broken; the problem is that a green
area tally is being read as coverage it does not have. Both blocks carry real
sim suites, so this is about what FORMAL adds, not about whether the blocks
work.
**Status:** OPEN. Measured 2026-10-01 while porting the proofs from
`formal/pumice`. Both were already disabled in pumice's wrappers; the port
inherited the gaps along with the properties.

## dfi_cdc: was 5 of 7 commented out, now 4

Live: `a_pinit_start_sticky`, `a_init_complete_sticky` (both verified to bind
-- a mutation making `init_complete_o` non-sticky is caught) and, as of
2026-10-01, `a_no_extra_staged`.

Still commented out: `a_token_per_burst`, `a_token_iff_last`, `a_istart_edge`,
`a_icmp_edge`. All four need HIERARCHICAL names (`dut.w_wtok_push`,
`dut.w_istart_push`, ...) and the pumice wrapper records why that failed: the
block instantiates FIVE FIFOs and the flattened netlist has near-identical
names across them, so an earlier version demonstrably asserted on wires that
were not the source signals (`wd_ready_o` and `w_wd` both 1 while the net
probed as `w_wtok_ready` read 0 -- impossible of the real signals). That is a
sound reason to leave them out, and resolving it means checking the flattened
net names against the source instance by instance.

## wr_data_cam: the data property is guarded off

`a_sram_readback` is written and then disabled with `&& 1'b0`, and the pumice
wrapper's note explains why honestly: the shadow model reports a readback
mismatch (write 0xFF to SRAM addr 1, fetch addr 1, `r_rd_q` reads 0) that could
not be corroborated, and **four earlier versions of that wrapper were wrong
about this block** -- entry slot vs SRAM slot, commit-handshake attribution,
the shared snarf mover, read-during-write in the check. A fifth model producing
a counterexample was correctly not treated as a DUT defect.

That reasoning is sound and should be preserved. But the consequence is that
the CAM's central property -- a beat written is the beat drained -- rests on
simulation only.

## Done when

Either the properties are enabled and pass (which for `wr_data_cam` means first
building a shadow model that can be trusted, i.e. the real work), or each
disabled property is replaced by a stated reason in the wrapper header AND the
area's status reporting distinguishes "proved" from "has a passing proof". The
second is cheaper and is the honest minimum.

## Progress, 2026-10-01

**Corrects a wrong claim in the first version of this task.** It said the five
`dfi_cdc` properties "were commented during pumice's bring-up and nobody has
retried them since. Try that first; it is an afternoon." That was wrong -- four
of the five have a substantive blocker (hierarchical net names in a five-FIFO
block), documented in the wrapper, and are not a quick win.

The fifth WAS a quick win, and is done. `a_no_extra_staged` -- "the PHY never
pops more staged bursts than the controller completed", i.e. the CDC does not
FABRICATE a burst token across the clock boundary, which is the property a CDC
proof exists to give -- is port-only. pumice left it out because
`pwr_staged_pop_i` is a free input, so a counterexample was the environment
popping an empty FIFO rather than the DUT mis-staging. That reasoning was
right; the fix was not to weaken the property but to state the one thing the
PHY side actually guarantees, that it honours valid/ready:

    assume (!(pwr_staged_pop_i && !pwr_staged_valid_o));

A protocol contract, not a claim about `scoria_dfi_cmd_path`'s internals.

It took one correction on the way: the first counterexample was the WRAPPER's
counter, not the CDC. `f_last_beats` was held at zero while `f_past_valid <= 2`
even though the DUT was already out of reset, so a burst completed in that gap
went uncounted and its token -- popped later, inside the window -- looked
fabricated. Counting now starts at reset deassertion.

Mutation-verified: dropping `wd_last_i` from `w_wtok_push` (a token on every
beat rather than the last) makes `a_no_extra_staged` FAIL.

So the remaining work is the four hierarchical-name properties in `dfi_cdc` and
`wr_data_cam`'s `a_sram_readback` -- both real projects, neither an afternoon.
