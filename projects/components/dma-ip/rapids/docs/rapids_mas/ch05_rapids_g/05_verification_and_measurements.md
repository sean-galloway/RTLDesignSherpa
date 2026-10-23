<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# rapids-g Verification and Measurements

**Status:** Implemented (rapids TASK-034)
**Last Updated:** 2026-10-22

---

## Verification

| Suite | What it shows |
|---|---|
| `dv/tests/fub_g/test_rapids_g_equiv.py` | RAPIDS's `scheduler` and `scheduler_g` + firmware side by side (`rapids_g_equiv_tb_top`), 4 and 8 channels, 256 and 512 bits, same descriptors, engine models with different latencies per side. Every engine command, packet record, MonBus packet and state transition must match in order. The address sequences are also checked against an independent golden model (`RapidsGEquivTB.golden_cmds`: the byte-to-beat ceiling and `dma_address_gen`'s formula). Cells: linear, ext, reset_ext, backpressure, error_reset, reset_any (a channel reset in every state), hart_fault (every hart halted by an illegal word patched over its SUMMARY poll, found by encoding, faults its channels and restarts), perf. |
| `dv/tests/fub_g/test_scheduler_g_edges.py` | `scheduler_g` alone with the testbench as its firmware: every command and flag in every state, 57 checks; legal edges taken, the rest ignored and counted, CH_ERROR left only by a reset; the automatic COMPLETE -> IDLE -> FETCH -> XFER of an armed descriptor with a staged head, and the stop at a declined head. |
| `dv/tests/top_g/test_rapids_g_regpath.py` | Both gatlings run a test program that reads and writes their own half's registers (`SCHED_TIMEOUT_CYCLES`, `SCHED_TIMEOUT_LIMIT`, `CH_SCRATCH`) through the mailbox while the host hammers the same command queue: every hart reads its own half's value, each gatling's writes land in its own half only, no host read is wrong. |
| `dv/tests/macro_g/` | Every RAPIDS `scheduler_group_array` test on `scheduler_group_array_g`, at 4 and 8 channels. |
| `dv/tests/top_g/` | Every RAPIDS `rapids_top` and `rapids_cxs_top` test, unchanged, on `rapids_g_top` and `rapids_g_cxs_top` (the 16-channel cells skip). |

: Table 5.5.1: rapids-g suites

The test files are RAPIDS's own: the -g runners load the RAPIDS cocotb tests by module name (`macro_g`) or re-host the RAPIDS wrappers (`top_g/rapids_g_rehost.py`), so rapids-g is held to exactly RAPIDS's checks. They caught a firmware race on the way: a head that arrived between the tight loop's HEAD_SUM and SUMMARY reads went down `service`'s slower path, and `tile_source_bad_ptype` saw its channel error after the test's wait on three of eight seed bases; the loop now re-reads HEAD_SUM before `service`.

Mutation: six firmware mutants (chain never followed, chain pre-armed wrong, beat ceiling off by one, stride sign, wrap mask dropped, the STATUS re-read in `refill_both` restored), six RTL mutants (edge-table holes for COMPLETE, ERROR, FETCH and the head flags; the fault interlock removed; auto-complete without the bases-done gate) and the register path's half pin each fail a test. Two survived the first bench and led to its state comparison and to the edge-table test.

Two RAPIDS bugs were found on the way and fixed in RAPIDS: rapids BUG-016 (a held CH_FETCH_DESC sent DESC_START every cycle) and rapids BUG-017 (stale EXT run bases after a channel reset; also in RAPIDS Beats and STREAM).

## Performance on the Board

rapids-8ch and rapids-g-8ch ran the same 45-point `gcompare` profile on the Genesys 2 harness
(`projects/fpga-systems/Genesys2/dma-ip/rapids/flows-rapids`): 8 channels, DATA_WIDTH 256, 100 MHz,
peak **3,200 MB/s per direction**. A figure is the bytes moved over the hardware timer's cycles
from the first request to the last write, descriptor fetch and launch included. Every point is
golden-checked and passes on both designs. The point names read `<group>_ch<N>_b<B>[_d<D>][_il]`:
`beat` is one descriptor per channel and `chain` a linked chain, `ch<N>` the active channels,
`b<B>` beats (32 bytes) per descriptor, `d<D>` descriptors per channel (absent: one), and `il` an
interleaved sink. Without `il` the sink stream feeds the channels one after another, so only one
channel holds data at a time; the source reads memory for every channel at once in every point.

Records: `reports/board/flow_results/byte_perf_gcompare_fsm_il_rc.json` (rapids-8ch) and
`byte_perf_gcompare_gfin_rc.json` (rapids-g-8ch).

The simulation of the board build (`make sim-gcompare`, run in seven chunks) matches the board
cycle for cycle: 85 of 85 windows on each design.
Matching needed one change to the host program. The shared descriptor engine's round-robin
pointer (`descriptor_engine_shared`, `r_rr_ptr`) is reset only by `aresetn`, so it carries from
one point to the next. A chunk that starts cold in simulation served the channels in a different
order from the board, where the previous point had run, and took 16 clocks longer (8 on
rapids-8ch). Each chunk after the first now runs the previous chunk's last point first, unrecorded
(`byte_perf.chunk_warmup`). The RTL is unchanged.

| Point | rapids-8ch sink | rapids-g-8ch sink | rapids-8ch source | rapids-g-8ch source |
|----------------------------------|-------------:|-------------:|-------------:|-------------:|
| beat_ch1_b1 | 54 | 14 | 50 | 14 |
| beat_ch1_b4 | 197 | 56 | 191 | 56 |
| beat_ch1_b16 | 624 | 210 | 648 | 212 |
| beat_ch1_b64 | 1,575 | 701 | 1,613 | 709 |
| beat_ch1_b256 | 2,544 | 1,693 | 2,568 | 1,703 |
| beat_ch1_b1024 | 3,006 | 2,617 | 3,015 | 2,624 |
| beat_ch1_b4096 | 3,149 | 3,031 | 3,152 | 3,033 |
| beat_ch1_b32768 | 3,194 | 3,178 | 3,194 | 3,178 |
| beat_ch2_b1 | 77 | 29 | 74 | 28 |
| beat_ch2_b4 | 281 | 111 | 281 | 110 |
| beat_ch2_b16 | 853 | 394 | 890 | 398 |
| beat_ch2_b64 | 1,896 | 1,151 | 1,941 | 1,160 |
| beat_ch2_b256 | 2,731 | 2,214 | 2,754 | 2,223 |
| beat_ch2_b1024 | 3,068 | 2,879 | 3,075 | 2,883 |
| beat_ch2_b4096 | 3,166 | 3,113 | 3,168 | 3,114 |
| beat_ch2_b32768 | 3,196 | 3,189 | 3,196 | 3,189 |
| beat_ch4_b1 | 99 | 45 | 100 | 45 |
| beat_ch4_b4 | 363 | 174 | 368 | 180 |
| beat_ch4_b16 | 1,056 | 589 | 1,095 | 621 |
| beat_ch4_b64 | 2,122 | 1,517 | 2,161 | 1,569 |
| beat_ch4_b256 | 2,840 | 2,505 | 2,857 | 2,540 |
| beat_ch4_b1024 | 3,102 | 2,993 | 3,107 | 3,005 |
| beat_ch4_b4096 | 3,175 | 3,145 | 3,176 | 3,149 |
| beat_ch4_b32768 | 3,197 | 3,193 | 3,197 | 3,194 |
| beat_ch8_b1 | 116 | 66 | 121 | 66 |
| beat_ch8_b4 | 425 | 252 | 436 | 250 |
| beat_ch8_b16 | 1,198 | 806 | 1,237 | 811 |
| beat_ch8_b64 | 2,257 | 1,837 | 2,291 | 1,843 |
| beat_ch8_b256 | 2,897 | 2,699 | 2,911 | 2,703 |
| beat_ch8_b1024 | 3,119 | 3,058 | 3,123 | 3,059 |
| beat_ch8_b4096 | 3,179 | 3,163 | 3,180 | 3,164 |
| beat_ch8_b32768 | 3,197 | 3,195 | 3,198 | 3,195 |
| chain_ch1_b1_d16 | 149 | 73 | 278 | 73 |
| chain_ch1_b64_d16 | 2,214 | 1,875 | 3,015 | 1,788 |
| chain_ch1_b1024_d16 | 3,113 | 3,103 | 3,188 | 3,177 |
| chain_ch1_b8192_d4 | 3,186 | 3,180 | 3,194 | 3,188 |
| chain_ch8_b1_d16 | 164 | 74 | 1,177 | 419 |
| chain_ch8_b64_d16 | 2,276 | 1,975 | 3,123 | 3,059 |
| chain_ch8_b1024_d16 | 3,121 | 3,117 | 3,195 | 3,191 |
| chain_ch8_b8192_d4 | 3,190 | 3,188 | 3,198 | 3,195 |
| beat_ch8_b16_il | 1,048 | 726 | -- | -- |
| beat_ch8_b64_il | 2,098 | 1,717 | -- | -- |
| chain_ch8_b1_d16_il | 822 | 418 | -- | -- |
| chain_ch8_b64_d16_il | 2,709 | 2,662 | -- | -- |
| chain_ch8_b1024_d16_il | 3,166 | 3,162 | -- | -- |

: Table 5.5.2: Genesys 2 gcompare, MB/s (peak 3,200; -- = not measured: the source side has no interleaved variant)

The firmware's cost per descriptor sets the gap. Its history on the hardest point, a one-channel
chain of 64-beat sink descriptors:

| Firmware | chain_ch1_b64_d16 sink | Clocks per descriptor |
|----------------------------------|-------------:|-------------:|
| first 8-hart image (one hart per channel) | 1,118 MB/s | about 288 |
| one-slot tight chain loop, HEAD_SUM re-read before `service` | 1,833 MB/s (board) | about 90 |
| seven-instruction idle pass (this image) | 1,875 MB/s | about 90 |
| rapids-8ch, for reference | 2,214 MB/s | -- |

: Table 5.5.3: Firmware cost per chained descriptor

Before STAGE_ARM (Section 5.2) the same point cost 672 clocks a descriptor. The tight loop
(Section 5.3) follows a chained head in four instructions; the shorter idle pass recovered a 1-2%
dip on the eight-channel single-descriptor sink points (`beat_ch8_b4` to `b256`).

## Scheduler Limit

Measured with `cocotb_test_perf`: engines that take every burst in one cycle and never stall, so the
scheduler is the only limit; 8 channels and 8 harts, DATA_WIDTH 256, cycles at 100 MHz. The bench
runs both directions on every channel, twice the load of one RAPIDS half (each half moves one
direction).

| Scenario | rapids-8ch | rapids-g-8ch | rapids-g-8ch / rapids-8ch |
|----------------------------------|-------------:|-------------:|-------------:|
| 16 one-beat descriptors, one channel | 131 | 2,371 | 18x |
| 16 one-beat descriptors on each channel | 131 | 2,316 | 18x |
| 16 64-beat descriptors on each channel | 1,255 | 2,389 | 1.9x |
| 4 64 KB descriptors on each channel | 9,248 | 9,529 | 1.03x |
| 2 1 MB descriptors on each channel | 84,277 | 84,420 | 1.002x |
| EXT, runs of 4, 64 beats, 4 per channel | 407 | 40,433 | 99x |
| EXT, per beat, 64 beats, 4 per channel | 1,043 | 135,848 | 130x |
| EXT, runs of 256, 1 MB, 1 per channel | 29,574 | 72,329 | 2.4x |

: Table 5.5.4: Cycles to finish, schedulers alone

With one hart per channel the channels no longer share a hart, so one busy channel and eight
busy channels cost the same (2,371 and 2,316). On 4 harts the same rows were 7,215 and 14,139.
Pre-validation hides the firmware behind the descriptor in flight whenever the transfer outlasts
it: two 1 MB descriptors per channel finish 0.17% behind rapids-8ch, and what remains is each
channel's first descriptor. Descriptors shorter than the firmware's work still pay it in full.
EXT descriptors are limited by base generation: a base costs the firmware about 15-35
instructions, each NUM_HARTS clocks, against one cycle in `stream_run_addr_gen`, so with both
directions on every channel even 256-beat runs cannot be fed at the engines' rate. Custom gatling
instructions for DMA (`gatling_dma`) are the lever for that case.

## Area and Timing

`rapids_core` and `rapids_core_g`, out of context on the Genesys 2 part (xc7k325t-2), 8 channels,
DATA_WIDTH 256, `SHARED_ENGINES` 1, `USE_AXI_MONITORS` 0, 8 harts, placed and routed at 100 MHz:

| | rapids_core | rapids_core_g |
|---|---:|---:|
| LUTs | 68,773 | 76,958 (+11.9%) |
| Registers | 55,550 | 58,673 |
| Block RAM tiles | 64 | 70 |
| DSPs | 64 | 0 |
| WNS at 100 MHz | +0.601 ns | +0.393 ns |

: Table 5.5.5: Out-of-context results

The register arbiter (`rapids_g_reg_arb`) is in the top, outside `rapids_core_g`, and not in these
numbers. Per half, `rapids_seq_g` is about 1.95k LUTs (gatling about 1.39k of it); the sink half is
38,693 LUTs against 34,943 for `rapids_snk`, and the source half 37,180 against 32,746 for
`rapids_src`. The 4-hart build measured 76,350 LUTs, 56,645 registers, 69 block RAM tiles and
+0.249 ns: eight harts cost about 600 LUTs and 2k registers, and gatling's own path is no longer
the worst. The worst path of `rapids_core_g` is now in the source half, from a scheduler's source
address (`gen_schedulers[3].u_scheduler/u_core/r_src_addr_reg`) to the AXI read engine's
outstanding counter enable, 20 levels. The 64 DSPs of `rapids_core` are the run-base generators'
index-by-stride multipliers, which the firmware replaces with additions.

In the full Genesys 2 harness of Table 5.5.2, rapids-g-8ch takes 110,662 LUTs (54.3%), 65,083
registers, 58 block RAM tiles and no DSPs and closes 100 MHz at +0.072 ns; rapids-8ch takes
100,007 LUTs at +0.357 ns.
