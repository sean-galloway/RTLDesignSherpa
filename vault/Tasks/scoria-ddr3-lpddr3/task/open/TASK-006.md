# TASK-006: two formal/scoria proofs are weak, and the area tally hides it

`formal/scoria` reports 9 blocks passing. Measured across the wrappers there
are **81 live assertions and 6 disabled**, and the disabled ones are not spread
thinly -- they are concentrated in two blocks, which therefore prove much less
than their green status suggests.

| Block | live | disabled | what is NOT proved |
|---|---|---|---|
| `dfi_cdc` | 2 | 5 | everything except the two sticky init latches |
| `wr_data_cam` | 3 | 1 | `a_sram_readback` -- the data-integrity property |
| the other 7 | 76 | 0 | -- |

**Priority:** P2. Nothing is known to be broken; the problem is that a green
area tally is being read as coverage it does not have. Both blocks carry real
sim suites, so this is about what FORMAL adds, not about whether the blocks
work.
**Status:** OPEN. Measured 2026-10-01 while porting the proofs from
`formal/pumice`. Both were already disabled in pumice's wrappers; the port
inherited the gaps along with the properties.

## dfi_cdc: 5 of 7 commented out

Live: `a_pinit_start_sticky`, `a_init_complete_sticky` (both verified to bind
-- a mutation making `init_complete_o` non-sticky is caught).

Commented out: `a_token_per_burst`, `a_token_iff_last`, `a_no_extra_staged`,
`a_istart_edge`, `a_icmp_edge`. So the block's actual job -- one token per
complete burst crossing the clock boundary, no extra staged beats -- is not
proved at all. That is the property a CDC proof exists for; what remains is two
latches.

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

A third option worth considering for `dfi_cdc`: the five commented properties
may be re-enablable as-is -- they were commented during pumice's bring-up and
nobody has retried them since. Try that first; it is an afternoon, not a
project.
