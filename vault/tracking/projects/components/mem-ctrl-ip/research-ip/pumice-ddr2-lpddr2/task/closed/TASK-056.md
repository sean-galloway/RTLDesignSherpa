# TASK-056: granite pick core, bank timers, CSR -- the three of the 5.15 list

> Source: owner, 2026-10-24, on the list closing TASK-055: "Do 1/2/3 now."
> (1) the pick core, 5 009 ASAP7 cells and never attributed below the block;
> (2) the bank timers, eight copies of five 8-bit counters for timings that
> never exceed 7 at this clock; (3) a granite CSR map that was pumice's 66
> registers verbatim, 25 of them wired to nothing. Related: TASK-054 / 055
> (method), handbook `design/variable-part-select-is-a-shifter.md`.

**Priority:** P2
**Status:** closed 2026-10-24 (board 4 107 -> 4 015 LUT, 2 695 -> 2 575 FF, +0.492 ns; pick core 5 407 -> 2 862 ASAP7 cells; cycle-identical on every cell)
**Owner:** TBD

## What landed

1. **Pick core payload by array index** (`mc_bank_pick`, shared, no knob):
   the fire payload's row / column lookup was `wr_slot_row_i[slot*ROW_WIDTH
   +: ROW_WIDTH]` on the flat N x ROW_WIDTH bus -- a barrel shifter over the
   whole bus, 1 538 of the block's 5 407 cells by source-line attribution.
   The vectors are unpacked into arrays and indexed; cycle-identical by
   construction and measured. **`HAS_STALL_STATS`** on the pick core and the
   plane: the eight 32-bit stall-cause counters are a generate; granite
   passes 0 (it wires no STALL_* CSRs, the outputs were open), pumice keeps 1.
2. **`BANK_TW`** (mc_bank_timers `TW`, plumbed through the plane and granite's
   chain): the per-bank timer width. The timing CSRs stay 8 bits and a value
   above the timer's range saturates to its maximum (conservative). Granite
   defaults to 5: DDR2 bank timings at <= 100 MHz fit (tRC 60 ns = 6 cycles).
3. **Granite's CSR map narrowed** (`regs/granite_csr.rdl`, regenerated with
   `bin/peakrdl_generate.py -o regs/generated --no-html`): 59 -> 35
   registers. Gone: the telemetry counters (PAGE_STATS_*, SCHED_STATS_*,
   REF_STATS_*, STALL_*, the OBS_ROW_HIT regfile, STATUS_HISTORY) and
   pumice's research / LPDDR2 configuration (SCHED_TUNING, INIT_TUNING,
   REF_CTRL, REF_TIMING_PB, PASR_*, TEMP_DERATE). Every remaining register
   keeps its address, so the map is a strict subset of pumice's. The harness
   host reads the controller by name through pumice's regmap (ddr2_char.py)
   and guards its telemetry reads with try / except, so a missing register
   degrades to "no telemetry"; nothing the granite flow writes was removed.

## Measured

ASAP7, blocks synthesized alone at granite's parameters (comb cells / flops):

| block | before | after |
|---|---|---|
| mc_bank_pick | 5 407 / 224 | 2 862 / 224 (array index, stall counters off) |
| mc_bank_timers x 8 | 2 181 / 440 | 1 667 / 320 (TW 5) |
| granite_top_geared, final text | 24 999 / 4 226 | 21 155 / 3 842 / 6 258 |

Board (Nexys A7, 75 MHz, granite_core LUT / FF, WNS, 0 failing endpoints):

| build | LUT / FF | WNS |
|---|---|---|
| TASK-055 defaults | 4 107 / 2 695 | +0.277 ns |
| pick payload by array index | 4 173 / 2 696 | +0.287 ns (Vivado already built a mux; the 66 LUT is build-to-build shuffle) |
| + BANK_TW 5 | 4 011 / 2 575 | +0.105 ns |
| + narrowed CSR (BANK_TW still 8 in this build) | 4 144 / 2 696 | +0.624 ns |
| committed text rebuilt as plain defaults (writes `fpga/reports`) | 4 015 / 2 575 | +0.492 ns, 0 / 96 777 |

Perf proxy against the TASK-055 defaults: the pick-payload lane and the
BANK_TW 5 lane are cycle-identical on every cell (1 and 8 threads, all
families, mixed); the narrowed-CSR lane is cycle-identical too (1 and 8 threads, mixed), with no register-lookup error in the host log; the final defaults rerun as plain defaults are cycle-identical at 1 and 8 threads and on mixed..

## Gates

Contract battery 12 / 3 strict xfailed (pick core); granite suite 6 / 1
xfailed on the TASK-055 knobs, with BANK_TW 5, on the narrowed CSR and on
the final defaults; pumice `run-all-func-both` 218 / 218 both geometries on
the shared pick core and plane (pumice keeps TW 8 and its stall counters);
lint 0 errors on granite_core and granite_top_geared at every setting and on
pumice_core with both cores. Board md5 == working text for the final build.
