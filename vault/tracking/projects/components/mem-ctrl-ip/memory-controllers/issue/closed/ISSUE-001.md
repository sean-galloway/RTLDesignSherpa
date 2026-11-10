# ISSUE-001: pumice/granite microarchitecture is ASIC-shaped for an FPGA target

> Source: owner, 2026-11-05: "reviewing the data from the last couple of months
> tells me the uarch is wrong for an fpga. I coded it all as if it were an asic.
> CAMs especially need to be handled correctly for FPGAs." Scope: the shared
> `common-ip` RTL as built by pumice (research) and granite (product) on the
> Nexys A7 (xc7a100t-1), Genesys 2 secondary.

**Priority:** P1 -- it is the structural reason pumice holds only 50 MHz, granite
sits at 0.004-0.021 ns of margin at 100 MHz, and the A7 is 95% slice-full with 2 of
135 BRAM tiles in use.
**Status:** CLOSED 2026-11-08 03:05 -- resolved into MC-004..MC-010 (five closed, MC-009 deferred for step (b), MC-004/MC-005 carry their own remaining phases); 12 of 17 rows done or closed on measurement (1, 2, 2b, 3, 4, 6, 8, 9, 10, 11, 12, 13, 16 with MC-004/005 active), 4 deferred with the number that says why (5, 7, 14b, 15); pumice closes 75 MHz on the FPGA SKU (+0.230 / 38,970 LUT) and runs on the board at 75 MHz, granite sys100 is at 0.000 ns. (2026-11-07 evening: rows 3, 9, 12, 13, 16 and the request half of 11 closed by e1ebaacf7 / 9e0f923b3; row 14 step (a) in; the pumice sys75 FPGA-SKU build closes timing, WNS +0.021, 0 failing endpoints) -- every row is now a task: MC-004 (row 1) and MC-005
(row 2b) active since 11-06; MC-006..MC-010 filed 2026-11-07 for the rest, after
the owner's "try to knock out all of these; pumice at 75 MHz with all of the FPGA
optimizations". The issue closes when the table is empty and the pumice sys75
build has positive slack.
**Owner:** TBD
**Report:** [assets/issue001_fpga_uarch/00_FPGA_UARCH_REVIEW.md](../../../assets/issue001_fpga_uarch/00_FPGA_UARCH_REVIEW.md)
with five slice reports beside it (pumice CAMs, scheduler plane, granite store and
pick, AXI/DFI planes, Vivado report mining). Every claim carries a file:line.

## Measured anchors

Granite from the 2026-10-29 hierarchy report; pumice from a hierarchy report
generated from the routed checkpoint (same controller source and parameters).

| Block | LUT | Note |
|---|---|---|
| pumice_core | 11,257 | 2.06x granite_core (5,456) |
| mc_cmd_arbiter | 3,426 | 4.7x granite's mc_bank_pick (726); 22-27 LUT levels on its worst cone |
| mc_wr_data_cam + mc_rd_cmd_cam | 3,711 | 1.7x granite's whole store |
| granite 16 bank-queue FIFOs | ~1,770 | 32% of granite_core |
| granite merge CAM, store + ring | ~1,420 | ring body tripled in the commit that added it |
| gaxi_skid_buffer x49 | 6,366 | 17% of the chip, about 1 LUT per flop |
| storage arrays dissolved to flops by async reset | 35 pumice / 30 granite | the synth log's one reason, every time |
| **after MC-004 + MC-005 (2026-11-06, synth-level A/B, same tree)** | pumice 46,131 -> 43,868 LUT, 35,671 -> 34,942 FF; granite 41,036 -> 38,877 LUT, 34,075 -> 33,417 FF | dissolved arrays 34 -> 17 / 28 -> 17, the 17 left are bridge-generated (MC-005 phase 3) |

The passing pumice board build is a 50 MHz controller clock; it fails by 5.630 ns at
75 MHz and 9.005 ns at 100 MHz, the 60 worst paths all one arbiter cone.

## The seven habits (detail and alternatives in the report)

1. Content-addressable match as the default lookup (CAM window, merge
   combiners, snarf, ring shadow sweeps, bank head records, arbiter population
   matrices).
2. Recomputing per cycle what could be stored at insert (per-entry row hit,
   open-row demand, tail rows).
3. Many small controllers instead of one memory with regions (16 bank-queue
   FIFOs, 8 bank timers each redoing the CSR arithmetic).
4. Flops where the fabric has RAM: every array written under `ALWAYS_FF_RST`
   (unconditionally async) is dissolved to registers; the skid buffer is a
   4-way-mux-per-bit shift register with data reset.
5. Same-cycle cones across plane boundaries (arbiter 1b into 1a, fire cone into
   CAM readies and clock enables, snarf round trip, FIFO flags from next
   pointers, the narrow pack through the host edge).
6. ASIC arithmetic (16-bit free-running ages, a max tree over 16 CSRs for a
   constant, barrel-shift address mappers on a live CSR).
7. Features the board cannot show a benefit for (merge, snarf, runtime QoS,
   population pick modes, the N=16 CAM default).

## Resolution path

Converge the FPGA product on granite's shape (per-bank FIFO store + bank pick)
and rework its implementation; keep pumice as the research core at N=8 with
merge and snarf off; apply the cross-cutting fixes to both via `common-ip`.
Each item below becomes a task when picked; the owner chooses the order.

| # | Rework | Saving (est.) | Risk | Task |
|---|---|---|---|---|
| 1 | two-register `gaxi_skid_buffer`, no data reset, no shift | ~3k LUT chip-wide | low | **MC-004**, active 2026-11-06 |
| 2 | bank queues as one RAM64M per direction + 3-entry head shift registers | ~1,300 LUT, fixes granite's worst-path tail | medium | **MC-010** row 2 done 2026-11-08: `mc_bank_queue` when HAS_AGE = 0 (formal equivalence vs the age FIFO; granite suites both ways); granite sys100 37,909 LUT, -224 |
| 2b | every storage array out of `ALWAYS_FF_RST` into a reset-free block with a small valid vector | hundreds of LUT, thousands of FF to LUTRAM | low | **MC-005** CLOSED 2026-11-10: common-ip + harness 2026-11-06 (routed -579 / -737 FF with MC-004), the bridge generator 2026-11-10 (bridge TASK-024, 17 -> 0 arrays per controller, -176 FF each); one dead merge array remains on the granite SKU, cost zero |
| 3 | merge off on the FPGA SKU; adjacent-pair coalesce at the intake if the half-width cell matters | granite ~1,420 LUT; pumice +473 LUT and its 75 MHz failure | low | **MC-006** done 2026-11-07 (e1ebaacf7: `WR_MERGE_EN`/`RD_MERGE_EN` off on the FPGA SKU; no intake coalesce yet) |
| 4 | ring shadow readiness evaluated at fetch; drop `r_src` reset value; delete dead `r_resp` | 150-250 LUT, 384 async-set flops | low | **MC-008** done 2026-11-08 (6999eeda1: readiness at fetch, `r_src` reset-free; `r_resp` is live and stays) |
| 5 | slot payload in reset-free LUTRAM; row carried in the queue entry | ~300 LUT, ~600 FF | medium | **MC-008** DEFERRED 2026-11-08: area only (~300 LUT / 600 FF) with timing closed; the arbiter-scanned fields must stay flops |
| 6 | hoist CSR-derived timer constants out of the 8 bank timers | 150-200 LUT; off granite's worst path | low | **MC-007** done 2026-11-08 (387970896: loads and flags derived once in `mc_bank_timers`, registered) |
| 7 | SRL delay lines (or 5->3 counters) in bank timers; SRL window for tFAW | 250-400 LUT | medium | **MC-007** DEFERRED 2026-11-08, measured: timers at the head of neither worst path after row 6; semantics risk for 250-400 LUT |
| 8 | FAST_RD_RELEASE `S_MAX` as a CSR or serial scan | ~180 LUT, 98 FF | low | **MC-007** done 2026-11-08 (6999eeda1: `S_MAX` by serial scan) |
| 9 | snarf: delete, or register `snarf_hit_o` | 150-250 LUT, all rd_cam failing endpoints | low | **MC-006** done 2026-11-07 (e1ebaacf7: `HAS_SNARF=0` on the FPGA SKU) |
| 10 | CAM ages as 8-bit prescaled counters | ~380 LUT, ~290 FF | low | **MC-008** CLOSED on the SKU 2026-11-08: age logic has no reader with `RUNTIME_PICK_MODES = 0` and `HAS_SNARF = 0`, synthesis removes it; research keeps 16-bit ages |
| 11 | register `timeout_pre_req`; FIFO flags from registered pointers | timing | low | **MC-007** done 2026-11-07/08 (9e0f923b3: `timeout_pre_req` registered; the FIFO flags were already registered, the CSR fold at the head of that path went with row 6) |
| 12 | `NARROW_EN=0` on the board netlist, or register the AW/AR rewrite | 250-350 LUT avoided | low | **MC-006** done 2026-11-07 (e1ebaacf7: `NARROW_EN=0` on the FPGA SKU) |
| 13 | address mapper: constant `bank_lsb` on the board or registered mask decode | 100-200 LUT | low | **MC-006** done 2026-11-07 (e1ebaacf7: one-hot constant slices, CSR stays live; formal family 4) |
| 14 | pumice arbiter: register the 1b shadows; hit/sibling flags into the CAM; pick modes build-time | ~2k of 3,426 LUT; the clock blocker | high | **MC-009** steps (a) 9e0f923b3 / 28571cf33 and (c) 6999eeda1 done; (b) DEFERRED, measured: the arbiter no longer holds the pumice worst path (+0.083..+0.230 on the SKU) |
| 15 | mc_bank_pick 16->8 rotor restructure, A/B on the proxy families | 150-250 LUT | high | **MC-010** DEFERRED 2026-11-08, measured: granite closes its 75 MHz board point by +0.494; the 100 MHz push profile sits within 25 ps of zero on the pick select loop across three builds |
| 16 | N=8 as the CAM backend's macro default | avoids 20k LUT at N=16 | none | **MC-006** done 2026-11-07 (e1ebaacf7: char macro default 8) |

## Defects found by the same reading, filed separately

- memory-controllers BUG-001 (B responses dropped without `wr_done` backpressure) -- fixed 2026-11-06.
- memory-controllers BUG-002 (DFI CDC token and data on separate synchronizers) -- fixed 2026-11-06.
- granite BUG-001 (same-id B order across banks; closes granite ISSUE-001) -- fixed 2026-11-06 with the AW-order B release queue.
- cdc BUG-004 (`glitch_free_n_dff_arn` has no `ASYNC_REG` attribute) -- attribute added 2026-11-06.

Also noted, not filed: `mc_dfi_cdc`'s same-clock branch samples across its two
named clock ports with no elaboration check (`:357-364`); `r_rd_q` driven from two
`always_ff` blocks in the store (`:848, :853`); `mc_head_rec_t` carries 32
constant-zero bits and an 8-bit slot for a 3-bit value.

## Postscript (2026-11-08 05:30)

After closure the owner stated the rule the review's rows 6, 11 and 13
should have been read through: every configuration CSR path into the
controller is a false path. Both board XDCs now carry it (whitelisted
PeakRDL field storage plus the harness CSR's static words; control pulses,
enables and status stay timed), validated on a routed checkpoint (489 + 166
flops selected, the CAL_CTRL pulses excluded). First measurement: the pumice
sys75 research configuration moves from -2.487 ns / 1,375 failing endpoints
to -1.665 / 1,255 with no RTL change; its worst path is now the read
intake's order-FIFO pointer into the arbiter's classify gate, a live flag.

## Postscript 2 (2026-11-08 06:25): granite FPGA SKU

Row 3 for granite: `GRANITE_FPGA_SKU` (store combiner off, narrow pack off)
takes granite from 37,900 to 35,712 LUT at sys100 (WNS -0.159 / 35 -> -0.013
/ 3, the pick loop either way) and closes the 75 MHz board point at +0.750
with 35,423 LUT. On why the sys100 research build moved from -0.023 to -0.159
under the false-path constraint alone: identical RTL, the same cone with the
same 12 logic levels, 0.13 ns more route -- the placer landed the pick region
differently once the CSR paths left its objective. That profile has now
produced +0.003, 0.000, -0.023, -0.159 and -0.013 on five builds; it is a
placement coin flip until row 15 shortens the loop.

## Postscript 3 (2026-11-08 07:50): the FPGA SKU is the configuration

Owner: "keep historical data for granite and pumice. however, we need to
converge on the fpga sku from here on out." Every top-level default is now
the SKU (pumice: combiners, snarf, narrow pack, runtime pick modes off;
granite: store combiner and narrow pack off); the research configuration is
the opt-in (`PUMICE_RESEARCH_CFG` / `GRANITE_RESEARCH_CFG` on the board and
in simulation, `CHAR_RESEARCH_CFG` for the char framework). The default
board builds reproduce the SKU builds byte for byte: pumice sys75 38,986 LUT
/ +0.164, granite sys75 35,423 LUT / +0.750. Every dated `reports_*`
directory from the research configuration stays committed as the history.
