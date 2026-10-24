# TASK-049: injector address modes -- a two-dimensional walk and an LFSR index (`row_thrash`, `random`)

> Source: owner, 2026-10-23 -- "You mentioned different traffic patterns
> friendly only to fr-fcfs. Can the injectors be updated to create those?"
> and "please make the injector updates." Related: TASK-046 (`mixed`, the
> two-thread form of the same conflict), TASK-045 (why the stream families
> could not separate the cores), TASK-043 (eight injectors on the board;
> this task also pipelines the read engine's error-bit popcount, that
> build's worst path).

**Priority:** P2
**Status:** closed 2026-10-23 (sim; board build of the eight-injector harness with this text: -0.212 ns, 36 failing endpoints (19 arbiter, 17 read engine 4), LUT 57 642 / FF 46 059 -- 91 percent of the xc7a100t; the popcount cone is gone from the list and what fails now is congestion. Eight injectors do not close 75 MHz on this part; the shipped harness default goes back to four (`CHAR_NUM_GEN` build knob for eight).)
**Owner:** TBD

## What landed

- `axi4_master_wr_injector` / `axi4_master_rd_crc_check` (rtl/amba/shared):
  the transaction index is shaped before `dma_address_gen`.
  `cfg_idx1_shift` = k feeds the index's low k bits to dimension 0 and the
  rest to dimension 1 (0 = the legacy one-dimensional walk, `index_1` held
  at 0 as before); `cfg_addr_lfsr` replaces the counter with a maximal
  16-bit Fibonacci LFSR (`ADDR_LFSR_TAPS`, x^16+x^15+x^13+x^4+1), one copy
  per address path stepped on that path's request accept, seeded with the
  data LFSR from `cfg_lfsr_seed` (bit 0 forced), so AW/W and AR/R stay in
  lockstep and a reader with the writer's seed reads the writer's sequence.
  Hammer mode keeps its meaning and wins over both. Both sampled at
  `cfg_start` with the rest of the program.
- `chargen_regs.rdl`: `AXI_ATTR.idx1_shift[27:24]`, `AXI_ATTR.addr_lfsr[28]`
  (reset 0 = legacy); block regenerated through `bin/peakrdl_generate.py`
  (rtl, docs, DV regmap copy). `char_gen_unit` wires both to every engine.
- Host `ddr2_char.py`: `idx1_shift` / `addr_lfsr` on `program_wr_engine` /
  `program_rd_engine`; `pumice_char.py`: `WINDOW_FAMILIES` names and the
  family doc block. Proxies: `perf_mixed_family.family_programs` programs
  `row_thrash` (thread g owns bank g: stride_0 = one row, k = 1, stride_1 =
  one burst wrapped in the page) and `random` (thread g owns rows 2g, 2g+1
  across all banks: LFSR index, stride_0 = one burst, wrap = region - 1);
  both proxies run them through the ordinary write-then-read flow.
- `axi4_master_rd_crc_check`: the mismatch XOR vector is registered before
  the `$countones` (TASK-043's eight-engine board build put that cone at
  -0.442 ns, 59 of 89 failing endpoints); the error-bit accumulate lands two
  cycles after the beat instead of one.
- TB tops / classes (`tb_axi4_master_pat_crc_pair.sv`, the two injector TB
  classes) connect and reset the new ports. Framework doc:
  `projects/fpga-systems/rtl/mem_char_framework/docs/address_modes.md`.

## Measured (perf proxy, board geometry, 75 MHz, pumice harness, wr / rd MB/s, mismatched 0)

| family | threads | FR-FCFS (TASK-048 text) | BANK_PICK | ratio |
|---|---|---|---|---|
| `row_thrash`, 2-beat bursts | 1 | 269.4 / 302.9 | 128.7 / 142.9 | 2.1x |
| `row_thrash`, 2-beat bursts | 8 | 285.5 / 286.1 | 283.0 / 280.5 | 1.0 |
| `random`, 8-beat bursts | 1 | 460.1 / 490.8 | 471.1 / 484.3 | 1.0 |
| `random`, 8-beat bursts | 8 | 430.6 / 479.3 | 406.3 / 444.0 | 1.06 / 1.08 |

One thread alternating two rows of one bank is the case the window exists
for: eight 2-beat bursts in the 16-entry window, the FR-FCFS core serves the
four A hits then the four B hits (two activates per eight bursts), the
per-bank head record alternates (eight). Mean latency 49 / 65 cycles against
95 / 95. At eight threads each bank sees at most two of its bursts in the
window, so there is nothing left to reorder and the two cores meet. The
random region (two rows by eight banks per thread) is a hit/miss mix in
random order: a tie at one thread, where the per-bank core's exact close
and the FR-FCFS core's armed close do the same work, and 6-8 percent to the
window at eight.

## Gates

val/amba injector tests, mem_char_framework dv (17), ddr2_char framework
functional suite, both perf proxies on the new families, lint of both
injectors and the engine block (only the pre-existing warnings), the
eight-injector board build: val/amba injector tests 285 / 292 on the first text (the 7 `fill_mismatch_err_bits` cells read the error-bit counter the cycle done rose, one cycle before the two-stage accumulate landed; done now settles two cycles) then 159 / 159 for the read-injector and pair files on the corrected text; mem_char_framework dv 17 / 17; ddr2_char framework functional suite 222 / 2 xfailed, and on the loaded machine a second run failed 10 cells "did not complete" that pass 10 / 10 alone (ISSUE-024, wall-clock engine wait); both proxies on the new families (table above); pumice 218 / 218 both geometries, granite 6 / 1 xfailed, common-ip 25 / 3 xfailed, formal PASS, lints clean after the arbiter's timeout-branch guard dropped the STAGE-1b column shadow as well (the default build had missed by 0.118 ns on that path with the injector text). Default board build, four injectors: +0.014 ns, 0 / 112 789 endpoints, LUT 44 887 / FF 35 593 (the address LFSRs and index shaping cost ~2 000 LUT), built text == committed text.
