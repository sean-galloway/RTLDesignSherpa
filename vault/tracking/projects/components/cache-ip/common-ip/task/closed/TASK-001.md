# TASK-001: FPGA microarchitecture review of the shared L1 core, amber and jet

**Date:** 2026-11-06
**Priority:** P1
**Status:** CLOSED 2026-11-08
**Owner:** cache-ip

## Why

On the Genesys2 pair rigs the two L1s were 98k (amber) and 108k (jet) LUTs
for a design whose storage is 32 KB of data and a few KB of tags. The routed
checkpoints showed where it went: the tag array dissolved into 11,264 flops
plus ~23k LUT of read muxes per core (one `always_ff` writing WAYS distinct
addresses defeats RAM inference), the data array was 16k LUTRAM plus 8.7k
MUXF per core because its read was combinational, and every payload store
(victim line, WB buffer data, response ring, MSHR write data) was flops
because it carried the async reset or a whole-line read port.

## What was done

Items, each validated with Verilator (clean-all, func, gate) and on the board
in bins (bitstream, program, init+smoke, from-reset disjoint64k against the
20k cosim, perf sweep):

1. `l1_tag_array` per-way generate (one write address per process) -> RAM.
2. `l1_repl` LRU as a per-set rank word in LUTRAM.
3. `l1_data_array` `SYNC_READ` registered read, `l1_control` `DATA_SYNC_READ`
   address lead; both cores on block RAM (16 RAMB36 each).
4. Payload stores reset-free and beat-addressed: `l1_control` victim_line_mem
   (`l1_victim` is address+valid only, `l1_drain` reads by beat),
   `jet_wb_buffer` r_data with the snarf slot lock, `jet_rsp_seq` word ring,
   jet r_req_*/r_cmt_rdata/r_sn_wb_data.
5. `jet_control` v3 fixes found on the way: tag-read-address (same-tag
   adjacent-set false hit), snoop-safe rule without `~r_lk_valid` (pair-rig
   SEED 27994 deadlock, handbook [[holds-that-wait-on-the-fabric]]).
6. `reset_sync` `REPLICATED_OUT` output flop, set in all four cache tops
   (the synchronizer MSB drove ~24k CLR pins; recovery slack 0.139 -> 1.446).

Deferred by choice: the req skid flop in mux mode and the alloc-overlay CAM
chain (small). Open: common-ip ISSUE-001 (no `XILINX` macro in the Vivado
flow) and jet-mesi-l1 TASK-003 (hit latency).

## Result (Genesys2, 100 MHz, routed)

| | amber before | amber bin 8 | jet before | jet bin 10 |
|---|---|---|---|---|
| Slice LUTs | 98,033 | 17,185 | 108,429 | 21,700 |
| LUT as memory | 33,316 | 1,648 | 33,616 | 2,244 |
| F7/F8 muxes | 29,969 | 1,427 | 31,399 | 1,612 |
| Flip-flops | 47,455 | 19,699 | 61,600 | 24,440 |
| Block RAM tiles | 128 | 160 | 128 | 160 |
| WNS | +0.014 ns | +0.334 ns | +0.159 ns | +0.517 ns |
| Total power | 0.980 W | 0.727 W | 1.571 W | 0.840 W |

Performance: amber cycle-identical to the RTL and to its pre-review bins on
every config; the baseline bitstream's 3-7 percent higher thrash cycle counts
were false misses from a timing-marginal build ([[board-vs-rtl]]). Jet's
resident hit latency 5 -> 6 from the sync-read array (+2.4 percent on
thrash); everything after bin 5 cycle-identical. Both boards' from-reset
disjoint64k runs match the 20k Verilator cosim (rsp CRCs 0x6c206c22 /
0x84d28860).

Verification on the final RTL: common 214/214, amber 79/79, jet 60/60 func;
both Genesys2 harness gates 2/2; formal jet_control safety (64) / liveness
(176) / cover PASS; amber_control live + cover PASS, safety depth-126 BMC
re-running at close (an earlier run was SIGTERMed by another session at step
47 of 126). FULL-level DV was not run before the push (owner's call).

Docs: amber and jet MAS chapters, `docs/markdown/rtl-cdc/reset_sync.md`,
handbook [[sram-and-memories]], [[reset-and-clocking]], [[board-vs-rtl]],
[[decision-stage-reads-the-snapshot]], [[holds-that-wait-on-the-fabric]],
[[formal]] (engine measurements: abc pdr and suprove time out on these
control models; rIC3 untried).
