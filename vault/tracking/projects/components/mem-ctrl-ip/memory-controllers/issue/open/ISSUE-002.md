# ISSUE-002: the bank_interleave map runs at a third of the SKU model on the board (233-258 MB/s against 778)

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
**Status:** open 2026-11-17
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
