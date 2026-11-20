# ISSUE-002: the bank_interleave map runs at a third of the SKU model on the board (233-258 MB/s against 778)

> **Closed 2026-11-17.** The premise was a model configuration error: the board's
> `bank_interleave` preset (`pumice_char.py` ControllerConfig) is
> SCHEME_BANK_INTERLEAVE **with PAGE_POLICY_CLOSE**, and the model's
> `granite_sku100_bi` encoded the map and left the page open. Corrected, the
> model lands 389 / 389 against the board's 232-238 and the gap is the
> close-page hop cost of ISSUE-003. See the Resolution below.

> Source: memory-controllers MC-018, 2026-11-17. The granite SKU model
> (`granite_sku100_bi`: the GraniteSKU controller with the stream encoded under
> the board's `bank_interleave` map, bank_lsb 2) sustains 777-781 MB/s on every
> row-hit family and 774-780 on `col_major_interleaved`; the board's
> `bank_interleave` preset measures 232-238 MB/s on the same cells with the lane
> on (`char_granite_sku100def_every_2026-11-16.csv`) and 258 lane off
> (MC-017's controls), read latency ~234 MC cycles against ~58 under ROW_MAJOR.
> That is ~3.4 MC cycles per 8-byte beat on a stream whose DRAM side is one
> row hit per bank per beat, rotating banks.

> 2026-11-17 (ISSUE-004 closed): the SKU model gained the store's admission
> terms (the mixed cap at every push, a 4-slot admission stage, the decode's
> bank-timed request with the rank timers holding the fire). The
> `bank_interleave` rows that are ACT-bound moved further from the board:
> `col_major` bl4 / bl8 312 -> 389 (board 195-237 / 237-235), bl16 519 -> 777
> (238 / 234), `random` 312 -> 389 (238-258), `row_thrash` 697 / 689 -> 775 /
> 777 (233-258); the row-hit rows stay 778 / 781. A bank-ready ACT that tRRD /
> tFAW still block is now a lane candidate that fires the CK they open, two
> slots per hop on a tRRD-bound chain where the old model paid two and a
> half; the RTL's lane has the same form, so the board's ~3.4 cycles per beat
> is the pipeline the model never had, as this issue says.

**Priority:** P2 -- the preset is not the SKU's default map, but a factor of
three on a stream the model says is free is an RTL-side serialization nobody
has named, and it is in the pick core or the store that every other map uses.
**Status:** CLOSED 2026-11-17 -- the preset was mis-encoded in the model (open page); corrected, the remaining gap is ISSUE-003's hop cost, resolved into MC-021
**Owner:** TBD

## What the model rules out

The DRAM: one column per MC cycle to rotating banks has no timing bar (tCCD 1
MC, no ACT per beat once the eight rows are open). The scheduling rules the
model carries: the rotor serves eight single-entry bank queues at one column
per slot (`sku_main_col` 100 percent of slots on `incremental` under the map).
The close-on-drain term: with bank_lsb 2 the entry behind each head is the
same burst's next beat eight banks on, a different bank, so the head's
`behind_same_row` is false and every column auto-precharges -- but the model
pays that too (one ACT per beat on the lane, `lane_act` = the beat count) and
still holds 778. So the cost is in a term the model does not carry: the
decode -> fire pipeline on a per-beat ACT -> COL chain across eight banks, the
AXI burst chopper / narrow pack feeding eight banks from one burst, the read
return ring's ordering across banks, or the write fill arriving per beat.

## What settles it

`PERF_W_HOPS` / `PERF_PICK_PROBE` on the granite proxy under
`bank_interleave` (`TEST_FAMILIES=incremental`, the host preset), one run each
direction: the hop whose valid-without-ready names the stall, as MC-015 found
the write pool. If the chain is ACT -> COL per beat, the model's `sku_laneoff`
/ `sku_slot1` columns under the map say what a lane or a second slot buys.

Resolves into a memory-controllers task (an RTL change with its model delta) or
a recorded no-action if the preset is retired.

## Resolution (2026-11-17)

- **The preset.** `pumice_char.py`'s `"bank_interleave"` is `scheme=SCHEME_BANK_INTERLEAVE,
  page_policy=PAGE_POLICY_CLOSE`; the SKU campaign never ran the open-page
  interleave (`open_interleave`). The model's `granite_sku100_bi` had
  `page_close=False`; every bank was a row hit and 778 MB/s was an open-page
  number against a close-page board. Fixed in `char_model.py`
  (`page_close=True`), guarded by `test_board_presets_are_what_the_host_programs`,
  which reads the host's preset table.
- **The proxy reproduces the board** under the host's exact pair
  (TEST_ADDR_SCHEME 2, TEST_PAGE_POLICY 2): incremental 235.0 / 229.6 and
  col_major 234.9 / 226.7 MB/s against the board's 234 / 233 and 237 / 235;
  under scheme 2 + policy 1 it gives 757.9 / 751.4 (the model's old number).
  Nothing in the RTL serializes the interleaved stream per se.
- **What remains** is the corrected model at 389 / 389 against 232-238
  (+63 .. +67 percent; +100 on the two bl4 cells): the close-page chain. The
  RTL fires each ACT 3 cycles after the previous one (t_rrd 2 plus the
  registered ok) and leaves two empty slots after each column pair; the
  model fires at the timers (3.4 cycles per beat against 2.0). Measured with
  `PERF_DRAM_TRACE` + `PERF_PICK_PROBE`; the mechanism and the numbers are in
  `char_results/model_knob_grid_2026-11-17.md` section 3. That is ISSUE-003's
  hop cost on eight banks, and both resolve into **MC-021** (a `hop_lag`
  model term, then the RTL question).
- The knob grid (28 settings of the ISSUE-004 terms on this preset) moves
  no cell into tolerance; `req_bank_timing` off reads closer (312 against
  389) by adding half a cycle of waiting per hop, which is not the RTL's
  mechanism and is not adopted.

## Re-read against the MC-021 step-7 model (2026-11-19)

Every cell this issue named is inside the board compare's tolerance under one
setting (`char_results/compare_model_sku_vs_board_sku100s4_s7_2026-11-19.md`):
the eight-bank `bank_interleave` cells 388-389 against the board's 387-388
(incremental, row_major, col_major bl8 / bl16, interleaved bl8 / bl16), and
the two bl4 cells 283 / 389 and 246 / 322 against 283 / 388 and 243 / 317.
The close-page chain this issue left open was not one `hop_lag`: it was the
pick pipeline's registers (MC-021 step 1), the ACT spacing count (step 2,
BUG-004), the lane's slot (step 3), the record's hit lag (step 4), and the
leftover pick of a fired auto-precharge pair, which was an RTL change (step
5) that moved the two bl4 cells on the board from 258 / 351 and 242 / 253 to
283 / 388 and 243 / 317. Nothing of this issue remains.
