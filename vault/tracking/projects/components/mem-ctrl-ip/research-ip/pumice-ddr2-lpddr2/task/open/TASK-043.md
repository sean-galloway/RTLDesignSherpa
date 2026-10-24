# TASK-043: ddr2_char harness — eight injectors per direction

> Source: owner, 2026-10-22 — "100 MHz is a future goal. Each of the
> injectors should be able to run 8 threads at once." The load point that
> matters for pumice vs LiteDRAM is eight concurrent threads per injector;
> the harness tops out at four today.
> Related: mem-ctrl recovery plan Phase 3 report §5 follow-up (the
> four-generator streaming loss, FIXED 2026-10-22 by the second-cycle stale
> mask; 567 / 568 MB/s at four per direction), ISSUE-022 (closed the same
> day). The eight-per-direction number is still unmeasured: that is this
> task.

**Priority:** P1 (owner's load point)
**Status:** open -- sim side DONE 2026-10-22 (RDL widened to eight per
direction, global block 0x400 -> 0x600, engine block gathers eight, granite
harness / sim top / perf proxy carry NUM_GEN; `TEST_NUM_GEN=8` runs
integrity-clean on both proxies -- numbers in the Phase 3 report §5.1).
LiteDRAM's 2 / 4 / 8 exist too, through the new sim proxy
(`test_litedram_char_perf.py`, same injectors and observers; report §5.1).
Remaining: the board host GO / config loops at eight and the board
bitstreams (pumice, granite, LiteDRAM share the block).
**2026-10-23 (owner: "having 8 injectors should only be a param change on
the injectors"):** it is. The GO register already has eight start bits per
direction, `char_engine_block` checks NUM_GEN <= GO_BITS and <= NUM_BANKS,
the host reads the count from `GEN_CONFIG`, and the sim proxies have run
eight all day. `ddr2_char_harness` NUM_GEN 4 -> 8 (this commit). What the
flip exposed is AREA: the eight-engine harness is 53 807 LUT / 42 977 FF
(85 percent of the xc7a100t, from 42 888 / 34 026) and missed 75 MHz by
0.442 ns on 89 endpoints -- 59 in the read engines' error-bit popcount cone
(`$countones` of the 64-bit mismatch XOR), 20 in the arbiter (congestion).
TASK-049 pipelines the popcount (XOR registered before the count); the
build on that text: -0.212 ns, 36 failing endpoints (19 arbiter, 17 read engine 4), LUT 57 642 / FF 46 059 -- 91 percent of the xc7a100t; the popcount cone is gone from the list and what fails now is congestion. Eight injectors do not close 75 MHz on this part; the shipped harness default goes back to four (`CHAR_NUM_GEN` build knob for eight).
**Owner:** TBD

## What blocks eight today

`char_engine_block` (`projects/fpga-systems/rtl/mem_char_framework/rtl/`)
stops elaboration at `NUM_GEN > 4`: the GO register in `chargen_regs.rdl`
has four single-pulse start bits per direction (`wr_go0..3`, `rd_go0..3`).
The sim top (`ddr2_char_uart_tb_top`), `ddr2_char_harness` and
`ddr2_char_macro` already carry `NUM_GEN` (plumbed 2026-10-22), and the perf
proxy raises it with `TEST_NUM_GEN` (`"NUM_GEN": max(4, TEST_NUM_GEN)`), so
`TEST_NUM_GEN=8` reaches the engine block and trips its check.

## Work

1. `chargen_regs.rdl`: eight start bits per direction (`wr_go0..7`,
   `rd_go0..7`), same single-pulse semantics; any status / done field that
   is per-generator widens with it. Regenerate through
   `bin/peakrdl_generate.py <rdl> -o <generated dir> --no-html` (never raw
   peakrdl); every consumer of the generated regmap re-reads it.
2. `char_engine_block`: lift the `NUM_GEN > 4` check to `NUM_GEN > 8` (the
   `NUM_GEN <= NUM_BANKS` check stays); check the per-generator fan-out of
   the GO / done wiring for hard-coded 4s.
3. Host (`build-perf/host/ddr2_char.py`): `sync_gen_config()` reports the
   count from the hardware; the GO write and the per-generator config
   loops must take eight. The board bitstream decides its own `NUM_GEN`
   (area: eight write injectors plus eight read checkers on the xc7a100t;
   measure before raising the board default).
4. Perf proxy: `TEST_NUM_GEN=8` across the four families; the first
   measurement is the comparison the owner asked for. Then the board.

## Done when

`TEST_NUM_GEN=8` runs integrity-clean on the proxy and the board at the
8-per-direction point, the numbers sit in the Phase 3 report's §5 table
beside the four-generator row, and LiteDRAM's same-harness number at eight
exists for the comparison (the LiteDRAM flow shares `char_engine_block`).
