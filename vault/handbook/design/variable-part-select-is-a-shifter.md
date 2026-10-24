---
title: A variable part-select on a flat bus is a barrel shifter, not a mux
summary: `bus[idx*W +: W]` synthesizes as a shift of the whole bus by idx*W; indexing an unpacked array `arr[idx]` is an N:1 mux per bit. In granite's pick core the part-select form was 1 538 of the block's 5 407 ASAP7 cells; the array form is a quarter of that and cycle-identical (2026-10-24).
---

# A variable part-select on a flat bus is a barrel shifter, not a mux

**Rule:** when a field is looked up by a runtime index, keep the fields in an
unpacked array (`logic [W-1:0] arr [N]`) and index the array. Do not write
`bus[idx*W +: W]` on a flattened `N x W` vector: the synthesizer sees a shift
by a computed amount and builds a log-depth shifter over the WHOLE bus, then
takes the bottom W bits. Flat vectors are for ports; unpack them inside the
module (an `always_comb` loop of constant part-selects costs nothing).

## The case (pumice TASK-056)

`mc_bank_pick` reads the fire payload by slot from the storage plane's flat
`wr_slot_row_i` / `rd_slot_row_i` (N x ROW_WIDTH) and the column vectors,
written as `wr_slot_row_i[w_sel_slot*ROW_WIDTH +: ROW_WIDTH]`. Attributed
by source line on the pre-ABC netlist, those four part-selects were 1 538
of the block's 5 407 cells -- 43 percent of the pick core for a 23-bit
8:1 lookup per direction. Unpacking the vectors into arrays and indexing
them took the block to 2 862 cells (with the stall counters also off), and
every proxy cell stayed cycle-identical. Vivado was indifferent (it already
recognised the shape as a mux), which is why the board number had never
flagged it: the lesson is an ASIC one, and the asic-trials flow is where it
shows.

## How to check a design against it

1. `grep -n "+:" rtl/*.sv` and look at every index expression that is not a
   constant or a genvar.
2. Attribute by source line (the asic-trials pre-ABC netlist carries `src`
   on every `always_comb` cell); a single line in the tens of percent is
   this pattern or a priority chain.

Related: [[area-measure-by-hierarchy]] (how the attribution is taken),
[[per-bank-queues-admit-from-the-pool]] (the slot fields this looks up).
