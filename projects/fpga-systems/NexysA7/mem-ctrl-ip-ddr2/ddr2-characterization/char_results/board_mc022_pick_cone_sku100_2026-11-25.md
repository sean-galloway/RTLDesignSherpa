# MC-022: the pick cone restructured exactly -- the sys100 SKU closes on two placements with no behaviour change

> memory-controllers MC-022, 2026-11-25. Candidate 1 of the task (exact
> restructurings, the golden copy unchanged). The behaviour-changing
> candidates (the pop a cycle after the fire, a request-register stage) were
> not needed. Granite SKU, 100 MHz, the 0.2 ns setup-uncertainty budget,
> Nexys A7.

## 1. What bound

MC-025's build A (default placement) read -0.255 ns, 19 failing, 14 of them
on the pick cone: `r_self_stale` / `r_is_col` / `r_win_pair` / `r_rfc_cnt` ->
`r2_pair` / `r2_cls` / `r_win_cls` / `r_win_pair` / `r_self_stale`, 10 .. 16
levels, ~72 percent route. The worst (`r_self_stale[15]` -> `r2_pair[0]`, 13
levels) ran through the lane pick into `rr_onehot`, and two of its levels
were the CARRY4s of `rr_onehot`'s `f & (~f + 1)`.

## 2. The two changes (`mc_bank_pick.sv`, both exact)

1. **`rr_onehot` in parallel.** The serial form filtered the set by age (a
   16-wide OR and a mux), then by the rotor (another OR and mux), then
   isolated the lowest bit through the +1 carry chain. Now: four lowest-bit
   isolations, each "bit i set and no lower bit set" in LUTs (`lsb_onehot`),
   on aged-and-at/above-rotor, aged, at/above-rotor and the whole set, and a
   4:1 select on two any-flags. The lane pick's own copy of the age filter
   in front of the call (idempotent with the function's first step) is gone.
2. **The main winner's index and the hint-class check per source.** After
   the class select, `w_pick_pair` was re-derived serially from the selected
   set (age refine, rotor filter, 16-to-4 priority encode), and the "the set
   is exactly the hinted pair" class override was a 16-bit compare on it.
   The per-source one-hots `w_oh_*` already carried the same pick, so the
   index is now the encode of each (`oh_enc`) muxed by `w_sel_src`, and the
   hint check is the per-source compare of the age-refined set, also before
   the select.

## 3. Formal (`formal/mc_common/mc_bank_pick`)

- All seven tasks pass on the final RTL (flat rebuilt from it) against the
  unchanged golden copy (`mc_bank_pick_gold.sv`, the serial forms):
  `equiv` (BMC 20, 652 s), `equiv_n4`, `dual` (prove), `cover`,
  `dual_cover`, `rdprio`, `rdprio_cover`.
- Mutation, on a scratch copy of the flat: `oh_enc` without the top index
  FAILS `equiv` (`a_all`, step 0); `lsb_onehot` ignoring bit 0 FAILS.
  Forcing the hint check false on the row source PASSES. A cover on that
  case (hint valid, row source selected, the refined row set equal to the
  hinted pair) is unreached at depth 20, where the harness's own covers are
  reached at steps 2 .. 4: the row source is only selected under a valid
  hint when the hint is a column hint, and then the hinted pair has no row
  request. The rewrite keeps the case anyway, computed as the original was.

## 4. Timing

Out of context, the pick core alone at granite's parameters (place, route,
the budget; I/O false-pathed, so only relative):

| RTL | WNS | failing | TNS | LUT |
|---|---|---|---|---|
| HEAD (MC-025) | -2.307 | 101 | -53.6 | 2,061 |
| + `rr_onehot` parallel | -1.617 | 29 | -17.6 | 2,224 |
| + index / hint per source | **+0.104** | **0** | 0 | 2,117 |

The worst path went from 16 levels (CARRY4 x3) to 10 LUT levels with no
carry chain.

The sys100 SKU bitstream (`GRANITE_SYS_100=1 make bitstream`):

| build | placement | MC-025 RTL | this RTL | failing |
|---|---|---|---|---|
| A | default | -0.255 | **+0.039** | 0 |
| B | `ExtraTimingOpt` | +0.001 | **+0.136** | 0 |

37,322 / 37,326 LUT (+42 on MC-025's 37,280). A's worst path is still the
pick select (`r_req` -> `r_win_cls`, +0.039); B's is the store's head record
-> `r_batch_done` (+0.136). The store's fire -> pop class, which MC-022
recorded at -0.051, now sits at +0.18 .. +0.26 without being touched: the
pick logic in front of it is shorter. Bitstreams
`ddr2_char_granite_sku100_mc022{a,b}_2026-11-25.bit`.

## 5. Board: the same cycles as before the change

Build A, smoke `init write_read memtest` ALL PASS, then `windows` and
`every` at `TEST_REF_ALIGN=0` against MC-025's offset-0 runs
(`sku100mc025a0`, build B of that RTL):

| suite | rows | wr / rd cycles differ | mismatched |
|---|---|---|---|
| `windows` | 9 | 0 | 0 |
| `every` | 68 | 1 | 0 |

The one row, `defaults row_major_bl4`, wrote in 269,754 cycles against
269,753. It is not the change: two repeats of `defaults` on this bitstream
and one on MC-025's bitstream all read 269,753 on every row. It is a rare
one-cycle draw that refresh alignment does not remove (1 row in 263 across
the aligned runs so far), filed as ISSUE-008. With alignment, the board A/B
of an exact change reads to the cycle, the use MC-025 was built for.

## 6. Regressions (after `make clean-all`)

granite 29 passed; framework 228 passed; pumice 117 + 525 + 48 passed;
`test_mc_store_arbiter_contract` (common-ip, no Makefile; build dir
deleted first) 27 passed, 3 xfailed; scoria's 17 failures, the same set as
the MC-025 run (its stale unit TBs).
