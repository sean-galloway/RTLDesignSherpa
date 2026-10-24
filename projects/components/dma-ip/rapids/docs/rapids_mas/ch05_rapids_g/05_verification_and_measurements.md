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
| `dv/tests/fub_g/test_rapids_g_equiv.py` | RAPIDS's `scheduler` and `scheduler_g` + firmware side by side (`rapids_g_equiv_tb_top`), 4, 8 and 16 channels, 256 and 512 bits, one, two and four channels per hart (`NUM_HARTS`: 8 on 4, 16 on 16, 8 and 4), same descriptors, engine models with different latencies per side. Every engine command, packet record, MonBus packet and state transition must match in order. The address sequences are also checked against an independent golden model (`RapidsGEquivTB.golden_cmds`: the byte-to-beat ceiling and `dma_address_gen`'s formula). Cells: linear, ext, reset_ext, backpressure, error_reset, reset_any (a channel reset in every state), hart_fault (every hart halted by an illegal word patched over its SUMMARY poll, found by encoding, faults its channels and restarts), alg (next-address selectors: unrunnable ones invalid on both sides, selector 1 on gatling against the golden model's Z-order and refused by RAPIDS), perf. |
| `dv/tests/fub_g/test_scheduler_g_edges.py` | `scheduler_g` alone with the testbench as its firmware: every command and flag in every state, 57 checks; legal edges taken, the rest ignored and counted, CH_ERROR left only by a reset; the automatic COMPLETE -> IDLE -> FETCH -> XFER of an armed descriptor with a staged head, and the stop at a declined head. |
| `dv/tests/top_g/test_rapids_g_regpath.py` | Both gatlings run a test program that reads and writes their own half's registers (`SCHED_TIMEOUT_CYCLES`, `SCHED_TIMEOUT_LIMIT`, `CH_SCRATCH`) through the mailbox while the host hammers the same command queue: every hart reads its own half's value, each gatling's writes land in its own half only, no host read is wrong. |
| `dv/tests/macro_g/` | Every RAPIDS `scheduler_group_array` test on `scheduler_group_array_g`, at 4, 8 and 16 channels. |
| `dv/tests/top_g/` | Every RAPIDS `rapids_top` and `rapids_cxs_top` test, unchanged, on `rapids_g_top` and `rapids_g_cxs_top`; the 16-channel cells on `rapids_g_16ch_top` and `rapids_g_16ch_cxs_top`. |

: Table 5.5.1: rapids-g suites

The test files are RAPIDS's own: the -g runners load the RAPIDS cocotb tests by module name (`macro_g`) or re-host the RAPIDS wrappers (`top_g/rapids_g_rehost.py`), so rapids-g is held to exactly RAPIDS's checks. They caught a firmware race on the way: a head that arrived between the tight loop's HEAD_SUM and SUMMARY reads went down `service`'s slower path, and `tile_source_bad_ptype` saw its channel error after the test's wait on three of eight seed bases; the loop now re-reads HEAD_SUM before `service`.

Mutation (re-run on the executive image, rapids TASK-037, and the selector, TASK-035; each from clean against the equivalence bench, or the edge test where it owns the logic):

| Mutant | Where | Result |
|---|---|---|
| JUDGE never chains | firmware | caught at two slots per hart (8 on 4, 16 on 8); with one slot a chained head always takes the chain hook, so JUDGE never sees one |
| route out of an unarmed COMPLETE | firmware | survived: unreachable (below); the code is now `fw_fault` |
| stride sign extension | firmware | caught |
| wrap mask dropped | firmware | caught |
| XFER_DATA's `ptab` entry returns | firmware | caught |
| GEN_OK not written | firmware | caught |
| Z-order: y subtracts | firmware | caught (`alg`) |
| selector ignored (always selector 0) | firmware | caught (`alg`) |
| edge-table hole: COMPLETE always legal | `scheduler_g` | caught by the edge test; the bench cannot reach it, because the firmware never commands COMPLETE |
| fault interlock removed | `scheduler_g` | caught |
| HEAD_SUM ignores the selector | `scheduler_g` | caught (`alg`) |
| the latch ignores the selector | `scheduler_core` | caught (`alg`) |

: Table 5.5.2: Mutation, executive image

The first run left three survivors, and each said something different. JUDGE's chain decision is live only when a hart serves two slots, a configuration the bench did not build until it gained its `NUM_HARTS` axis. The edge-table hole belongs to the edge test. The unarmed-COMPLETE route, with the rest of the old hand path, cannot run at all: every valid head is staged armed, and the firmware takes a head itself only when it declined it, which the latch also calls invalid (Section 5.3). That code became the `fw_fault` row rather than a handler no test can reach.

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

The executive image with the next-address selector (rapids TASK-037 and TASK-035;
`byte_perf_gcompare_gexe_rc.json`, 2026-10-23) passes all 45 points on the board, matches its
simulation on 85 of 85 windows, and is identical to the 2026-10-22 image (gfin) on all 85: every
gcompare point is a linear descriptor whose head the poll stages itself, the path the rewrite did
not lengthen, so the board numbers in Table 5.5.3 stand unchanged. That build takes 111,738 LUTs,
65,246 registers and 58 block RAM tiles and closes 100 MHz at +0.061 ns. rapids-8ch's simulation,
on the shared datapath with the selector check, still matches its own board run on 85 of 85.
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

: Table 5.5.3: Genesys 2 gcompare, MB/s (peak 3,200; -- = not measured: the source side has no interleaved variant)

The firmware's cost per descriptor sets the gap. Its history on the hardest point, a one-channel
chain of 64-beat sink descriptors:

| Firmware | chain_ch1_b64_d16 sink | Clocks per descriptor |
|----------------------------------|-------------:|-------------:|
| first 8-hart image (one hart per channel) | 1,118 MB/s | about 288 |
| one-slot tight chain loop, HEAD_SUM re-read before `service` | 1,833 MB/s (board) | about 90 |
| seven-instruction idle pass (this image) | 1,875 MB/s | about 90 |
| rapids-8ch, for reference | 2,214 MB/s | -- |
| two slots per hart (16 channels), SUMMARY then JUDGE | 1,122 MB/s (board) | 184 |
| two slots, HEAD_SUM checks ahead of SUMMARY | 1,546 MB/s (board) | 134 |
| two slots, SUMMARY then the chain hook per slot (this image) | 2,008 MB/s (board) | 103 |
| rapids-16ch, for reference | 2,232 MB/s | 93 |

: Table 5.5.4: Firmware cost per chained descriptor (the 16-channel rows' clocks are the point's measured cycles / 16)

Before STAGE_ARM (Section 5.2) the same point cost 672 clocks a descriptor. The tight loop
(Section 5.3) follows a chained head in four instructions; the shorter idle pass recovered a 1-2%
dip on the eight-channel single-descriptor sink points (`beat_ch8_b4` to `b256`).

## Scheduler Limit

Measured with `cocotb_test_perf`: engines that take every burst in one cycle and never stall, so the
scheduler is the only limit; 8 channels and 8 harts, DATA_WIDTH 256, cycles at 100 MHz. The bench
runs both directions on every channel, twice the load of one RAPIDS half (each half moves one
direction).

| Scenario | rapids-8ch | rapids-g-8ch, 10-22 | rapids-g-8ch, executive | executive / rapids-8ch |
|----------------------------------|-------------:|-------------:|-------------:|-------------:|
| 16 one-beat descriptors, one channel | 131 | 2,371 | 2,371 | 18x |
| 16 one-beat descriptors on each channel | 131 | 2,316 | 2,316 | 18x |
| 16 64-beat descriptors on each channel | 1,255 | 2,389 | 2,389 | 1.9x |
| 4 64 KB descriptors on each channel | 9,248 | 9,529 | 9,412 | 1.02x |
| 2 1 MB descriptors on each channel | 84,277 | 84,420 | 84,443 (*) | 1.002x |
| EXT, runs of 4, 64 beats, 4 per channel | 407 | 40,433 | 39,201 | 96x |
| EXT, per beat, 64 beats, 4 per channel | 1,043 | 135,848 | 130,086 | 125x |
| EXT, runs of 256, 1 MB, 1 per channel | 29,574 | 72,329 | 70,641 | 2.4x |

: Table 5.5.5: Cycles to finish, schedulers alone

The executive image (rapids TASK-037) is 2-4% faster on every EXT row and unchanged on the
linear ones: an XFER_DATA step costs four instructions of dispatch and returns, where `service`
re-read STATUS and re-judged the head before returning. (*) The scenarios run in sequence in one
simulation, so when the 64 KB row finishes sooner the 1 MB row starts at another phase of the
barrel; run alone from the same cycle, both images take 84,420 (and 9,454 for 64 KB).

With one hart per channel the channels no longer share a hart, so one busy channel and eight
busy channels cost the same (2,371 and 2,316). On 4 harts the same rows were 7,215 and 14,139.
Pre-validation hides the firmware behind the descriptor in flight whenever the transfer outlasts
it: two 1 MB descriptors per channel finish 0.17% behind rapids-8ch, and what remains is each
channel's first descriptor. Descriptors shorter than the firmware's work still pay it in full.
EXT descriptors are limited by base generation: a base costs the firmware about 15-35
instructions, each NUM_HARTS clocks, against one cycle in `stream_run_addr_gen`, so with both
directions on every channel even 256-beat runs cannot be fed at the engines' rate. Custom gatling
instructions for DMA (`gatling_dma`) are the lever for that case.

### Sixteen Channels

rapids-g-16ch (rapids TASK-036): the same bench at 16 channels, DATA_WIDTH 256, with each way of
spreading the 16 channels over one gatling's harts, measured on the committed image (the two-slot
poll with the chain hook, Section 5.3).

| Scenario | rapids-16ch | 16 harts x 1 | 8 harts x 2 (default) | 4 harts x 4 |
|----------------------------------|-------------:|-------------:|-------------:|-------------:|
| 16 one-beat descriptors, one channel | 131 | 4,731 | 3,131 | 1,619 |
| 16 one-beat descriptors on each channel | 131 | 4,620 | 5,383 | 5,627 |
| 16 64-beat descriptors on each channel | 1,255 | 4,700 | 5,469 | 5,704 |
| 4 64 KB descriptors on each channel | 9,248 | 9,609 | 9,585 | 9,579 |
| 2 1 MB descriptors on each channel | 84,277 | 84,610 | 84,612 | 84,612 |
| EXT, runs of 4, 64 beats, 4 per channel | 407 | 78,362 | 77,998 | 77,714 |
| EXT, per beat, 64 beats, 4 per channel | 1,043 | 260,192 | 257,831 | 256,406 |
| EXT, runs of 256, 1 MB, 1 per channel | 29,574 | 140,577 | 139,688 | 139,184 |

: Table 5.5.6: Cycles to finish at 16 channels

Sixteen harts make every instruction cost a hart 16 clocks, which a lone busy channel pays in full
(4,731); four harts are best for one channel and on EXT, but lose 22% to sixteen when all sixteen
channels run one- or 64-beat descriptors, each hart walking four slots. Eight harts with two slots
each are 16% behind sixteen there, within 0.6% of the best on EXT, 1.5x faster than sixteen harts
for a single channel, and keep half the hart state; `rapids_seq_g` defaults to them at 16 channels.
Against the image this table first carried (the two-slot poll before the chain hook), the eight-hart
column is about 10% slower on the one- and 64-beat rows and 1.5% on EXT: this bench's descriptors
are independent (`next_ptr` = 0), so none takes the hook, and the SUMMARY-first pass costs a few
instructions per head. What the hook buys is on chains, which this bench does not run: Tables 5.5.9
and 5.5.10. The 1 MB rows are within 0.4% of rapids-16ch, the 64 KB rows within 3.6%.

## Sixteen Channels on the Genesys 2

rapids-g-16ch and rapids-16ch in the full Genesys 2 harness (rapids TASK-036), `make bitstream-perf CHANNELS=16 ROW_COL=1`, 2026-10-23. The first rapids-g-16ch build placed at 198,555 LUTs (97.4%, every slice) and did not route: the harness's two 2048-entry descriptor RAMs had fallen to distributed RAM (25.6k LUTs each), because `sdpram_core`'s byte-enabled write port will not map to block RAM. The harness writes whole descriptors, so it now builds them with `USE_WSTRB` = 0, as the STREAM harness does; the 8-channel bitstreams take the same saving, not yet re-measured.

| Bitstream | LUTs | WNS at 100 MHz | Board == simulation |
|---|---:|---:|---|
| rapids-16ch | 135,389 (66.4%) | +0.192 ns | 109/109 windows identical |
| rapids-g-16ch, ROM | 151,472 (74.3%) | +0.148 ns | 109/109 windows identical |
| rapids-g-16ch, `FW_WRITABLE` | 152,813 (75.0%) | +0.034 ns | 109/109 identical, the committed image loaded live |

: Table 5.5.8: 16-channel bitstreams

The 16-channel gcompare profile is 57 points: the 8-channel profile's single descriptors and chains, plus 16-channel single descriptors, chains at 1, 8 and 16 channels in size-major order, and the interleaved sink at 16 (`byte_perf.build_points`); in simulation it runs as 18 chunks to keep each under the 100 ms cap. "ROM" is the image before the two-slot chain hook; "v2" is the committed image (Section 5.3), loaded live on the writable bitstream with `--fw`.

| Point | rapids-16ch sink | rapids-g ROM sink | rapids-g v2 sink | rapids-16ch source | rapids-g ROM source | rapids-g v2 source |
|---|---:|---:|---:|---:|---:|---:|
| beat_ch1_b1 | 1,600 | 1,600 | 1,600 | 356 | 356 | 356 |
| beat_ch1_b256 | 2,643 | 1,736 | 1,625 | 3,103 | 3,103 | 3,103 |
| beat_ch8_b16 | 1,241 | 813 | 788 | 3,012 | 3,012 | 3,012 |
| beat_ch8_b256 | 2,913 | 2,704 | 2,686 | 3,188 | 3,188 | 3,188 |
| beat_ch16_b1 | 133 | 70 | 67 | 2,048 | 247 | 230 |
| beat_ch16_b16 | 1,309 | 974 | 938 | 3,103 | 2,626 | 2,498 |
| beat_ch16_b256 | 2,935 | 2,820 | 2,810 | 3,194 | 3,194 | 3,194 |
| beat_ch16_b32768 | 3,198 | 3,197 | 3,197 | 3,200 | 3,200 | 3,200 |
| chain_ch1_b1_d16 | 178 | 19 | 36 | 397 | 19 | 36 |
| chain_ch1_b64_d16 | 2,232 | 1,122 | 2,008 | 3,175 | 1,208 | 2,190 |
| chain_ch8_b1_d16 | 169 | 21 | 38 | 2,677 | 154 | 284 |
| chain_ch8_b64_d16 | 2,278 | 1,236 | 2,152 | 3,197 | 3,197 | 3,197 |
| chain_ch16_b1_d16 | 168 | 20 | 36 | 3,091 | 172 | 346 |
| chain_ch16_b64_d16 | 2,280 | 1,232 | 2,084 | 3,198 | 3,198 | 3,198 |
| chain_ch16_b1024_d16 | 3,121 | 3,119 | 3,120 | 3,200 | 3,200 | 3,200 |
| chain_ch16_b8192_d4 | 3,190 | 3,189 | 3,190 | 3,200 | 3,200 | 3,200 |
| beat_ch16_b16_il | 1,309 | 839 | 813 | -- | -- | -- |
| beat_ch16_b64_il | 2,351 | 1,879 | 1,845 | -- | -- | -- |
| chain_ch16_b1_d16_il | 948 | 155 | 292 | -- | -- | -- |
| chain_ch16_b64_d16_il | 2,772 | 2,702 | 2,738 | -- | -- | -- |
| chain_ch16_b1024_d16_il | 3,172 | 3,166 | 3,169 | -- | -- | -- |

: Table 5.5.9: Genesys 2 gcompare at 16 channels, MB/s (peak 3,200; -- = no source variant)

The two-slot chain hook roughly doubles the short chains (19 to 36 MB/s on one-beat descriptors, 1,122 to 2,008 on 64-beat ones) and costs single descriptors one to three instructions: 1-7% on the points where the firmware is the limit, nothing from 256 beats per channel up.

### Where rapids-g Catches Up

The sweep that sizes the gap, in simulation (`make sim-gscale CHANNELS=8|16`; the same simulation matches the board on all 109 gcompare windows): single descriptors and 16-descriptor interleaved-sink chains on every channel of the build, in 2x size steps, rows in beats per descriptor (32 bytes each). Each cell is rapids cycles / rapids-g cycles (1.00 = parity). Columns: `chain` is the 16-descriptor interleaved-sink chain (8 channels run one slot per hart; at 16, ROM is the image before the chain hook and v2 the committed one); `sink`, `source` and `il sink` are a single descriptor per channel, plain or with the sink streams interleaved.

| Beats | chain 8ch | chain 16ch ROM | chain 16ch v2 | sink 8ch | sink 16ch v2 | source 8ch | source 16ch v2 | il sink 8ch | il sink 16ch v2 |
|------:|-----:|-----:|-----:|-----:|-----:|-----:|-----:|-----:|-----:|
| 1 | 0.52 | 0.17 | 0.32 | 0.57 | 0.53 | 0.55 | 0.49 | 0.57 | 0.53 |
| 2 | 0.49 | 0.22 | 0.41 | 0.57 | 0.53 | 0.56 | 0.51 | 0.58 | 0.53 |
| 4 | 0.60 | 0.41 | 0.68 | 0.59 | 0.56 | 0.57 | 0.54 | 0.61 | 0.56 |
| 8 | 0.90 | 0.76 | 0.93 | 0.63 | 0.62 | 0.61 | 0.60 | 0.66 | 0.62 |
| 16 | 0.95 | 0.93 | 0.97 | 0.67 | 0.72 | 0.66 | 0.70 | 0.71 | 0.67 |
| 32 | 0.97 | 0.96 | 0.98 | 0.74 | 0.82 | 0.73 | 0.82 | 0.76 | 0.73 |
| 64 | 0.98 | 0.97 | 0.99 | 0.81 | 0.88 | 0.80 | 0.88 | 0.83 | 0.80 |
| 128 | 0.99 | 0.99 | 0.99 | 0.88 | 0.92 | 0.88 | 0.92 | 0.89 | 0.87 |
| 256 | 0.99 | 0.99 | 1.00 | 0.93 | 0.96 | 0.93 | 0.96 | 0.93 | 0.92 |
| 512 | 1.00 | 1.00 | 1.00 | 0.96 | 0.98 | 0.96 | 0.98 | 0.96 | 0.96 |
| 1024 | 1.00 | 1.00 | 1.00 | 0.98 | 0.99 | 0.98 | 0.99 | 0.98 | 0.98 |
| 2048 | -- | -- | -- | 0.99 | 0.99 | 0.99 | 0.99 | 0.99 | 0.99 |
| 4096 | -- | -- | -- | 0.99 | 1.00 | 0.99 | 1.00 | 1.00 | 0.99 |

: Table 5.5.10: rapids / rapids-g cycles, every channel busy

How much a channel must move per descriptor before rapids-g is within 10%, 5% and 1% of rapids, from
the sweeps (DATA_WIDTH 256, so 32 bytes a beat; the smallest size from which every larger size
in the sweep stays inside the bound), with every channel busy and with one channel busy on each build. A chain row is bytes per descriptor in a 16-descriptor chain,
so the channel moves sixteen times that in the run:

| Shape | Busy channels | Within 10% | Within 5% | Within 1% |
|------------------------------------|-------------:|-----------:|----------:|----------:|
| single descriptor, sink | 1 of 8 | 64 KB | 128 KB | 512 KB |
| single descriptor, sink | 8 of 8 | 8 KB | 16 KB | 64 KB |
| single descriptor, sink | 1 of 16 | 64 KB | 128 KB | 1 MB |
| single descriptor, sink | 16 of 16 | 4 KB | 8 KB | 64 KB |
| single descriptor, source | 1 of 8 | 64 KB | 128 KB | 512 KB |
| single descriptor, source | 8 of 8 | 8 KB | 16 KB | 128 KB |
| single descriptor, source | 1 of 16 | 64 KB | 128 KB | 1 MB |
| single descriptor, source | 16 of 16 | 4 KB | 8 KB | 64 KB |
| single descriptor, interleaved sink | 8 of 8 | 8 KB | 16 KB | 64 KB |
| single descriptor, interleaved sink | 16 of 16 | 8 KB | 16 KB | 128 KB |
| 16-descriptor chain, sink | 1 of 8 | 4 KB | 4 KB | 16 KB |
| 16-descriptor chain, sink | 1 of 16 | 2 KB | 4 KB | 32 KB |
| 16-descriptor chain, source | 1 of 8 | 4 KB | 8 KB | 16 KB |
| 16-descriptor chain, source | 1 of 16 | 4 KB | 8 KB | 32 KB |
| 16-descriptor chain, interleaved sink | 8 of 8 | 512 B | 512 B | 4 KB |
| 16-descriptor chain, interleaved sink | 16 of 16 | 256 B | 512 B | 4 KB |

: Table 5.5.11: Bytes per descriptor for rapids-g to be within 10%, 5% and 1% of rapids

The one-channel rows come from the same sweep run with one channel busy (`make sim-gscale1
CHANNELS=8|16`, both directions, chains plain rather than interleaved), on each build:

| Beats | chain sink (8ch build) | chain sink (16ch build) | chain source (8ch build) | chain source (16ch build) | sink (8ch build) | sink (16ch build) | source (8ch build) | source (16ch build) |
|------:|-----:|-----:|-----:|-----:|-----:|-----:|-----:|-----:|
| 1 | 0.49 | 0.22 | 0.26 | 0.12 | 0.27 | 0.26 | 0.28 | 0.27 |
| 2 | 0.53 | 0.24 | 0.26 | 0.12 | 0.27 | 0.26 | 0.29 | 0.27 |
| 4 | 0.62 | 0.28 | 0.26 | 0.12 | 0.29 | 0.27 | 0.29 | 0.28 |
| 8 | 0.56 | 0.36 | 0.27 | 0.12 | 0.31 | 0.29 | 0.30 | 0.29 |
| 16 | 0.48 | 0.45 | 0.44 | 0.20 | 0.34 | 0.32 | 0.33 | 0.31 |
| 32 | 0.54 | 0.60 | 0.78 | 0.36 | 0.38 | 0.35 | 0.37 | 0.35 |
| 64 | 0.85 | 0.90 | 0.59 | 0.66 | 0.45 | 0.42 | 0.44 | 0.41 |
| 128 | 0.96 | 0.96 | 0.92 | 0.95 | 0.54 | 0.51 | 0.54 | 0.51 |
| 256 | 0.99 | 0.98 | 0.99 | 0.98 | 0.67 | 0.63 | 0.66 | 0.63 |
| 512 | 0.99 | 0.99 | 0.99 | 0.99 | 0.78 | 0.75 | 0.78 | 0.75 |
| 1024 | 1.00 | 0.99 | 1.00 | 0.99 | 0.87 | 0.85 | 0.87 | 0.85 |
| 2048 | -- | -- | -- | -- | 0.93 | 0.92 | 0.93 | 0.92 |
| 4096 | -- | -- | -- | -- | 0.96 | 0.96 | 0.96 | 0.96 |
| 8192 | -- | -- | -- | -- | 0.98 | 0.98 | 0.98 | 0.98 |
| 16384 | -- | -- | -- | -- | 0.99 | 0.99 | 0.99 | 0.99 |
| 32768 | -- | -- | -- | -- | 1.00 | 0.99 | 1.00 | 0.99 |

: Table 5.5.12: rapids / rapids-g cycles, one channel busy (`--` = not in the sweep)


With one channel busy a lone descriptor has nothing to hide the firmware behind: against the FSM it
costs a fixed 162 clocks per single descriptor on the 8-channel build and 194 on the 16-channel one,
whose hart walks a second, idle slot each pass (the cycle gap is the same from 8 KB to 1 MB), so the
ratio is 1 - gap / beats: within 10% from 64 KB, 5% from 128 KB, and 1% from 512 KB (8 channels) or
1 MB (16).
A chain on one channel overlaps the next head with the running descriptor and is within 5% from 4-8 KB
and 1% from 16-32 KB; the 16-channel build is later on chains below 2 KB because its hart walks a second,
idle slot every pass. With every channel busy the other channels' data hides the cost, which is why
those rows close eight times earlier.


Chains close the gap at 512 bytes (the 8-channel chain reads 0.90 at 256 B in Table 5.5.10 but is 0.899) and are within 1% at 4 KB on both builds; a single descriptor per
channel needs 8-16 KB to be within 5% and 64-128 KB to be within 1%, because its whole firmware cost
(fetch, judge, stage and complete, with no next head to overlap) is paid once per descriptor against a
data phase that only grows with the size. With one gatling per half serving 16 channels the expectation was that chains need twice the size to catch the FSM, since each hart serves two channels: on the ROM image they did (0.95 at 16 beats on 8 channels, at 32 on 16). With the chain hook in the two-slot poll they catch up at 16 on both, and are ahead of the 8-channel build from 4 beats; one- and two-beat chains remain behind it (0.32-0.41 against 0.49-0.52), the cost of walking two slots per pass. Single descriptors are at most 0.04 behind the 8-channel build at any size (and ahead of it on the plain sink from 16 beats, where rapids-16ch slows too): the firmware's work is per descriptor, so more channels do not move it.

## Area and Timing

`rapids_core` and `rapids_core_g`, out of context on the Genesys 2 part (xc7k325t-2), DATA_WIDTH
256, `SHARED_ENGINES` 1, `USE_AXI_MONITORS` 0, `USE_ROW_COL_MAJOR_ADDRESSING` 1, default harts (8 at
8 channels, 8 at 16), placed and routed at 100 MHz, measured 2026-10-23 on the executive image with
the next-address selector:

| | rapids-8ch | rapids-g-8ch | rapids-16ch | rapids-g-16ch |
|---|---:|---:|---:|---:|
| LUTs | 69,184 | 77,975 (+12.7%) | 126,820 | 141,067 (+11.2%) |
| Registers | 56,105 | 58,837 | 101,808 | 104,738 |
| Block RAM tiles | 64 | 70 | 128 | 134 |
| DSPs | 64 | 0 | 128 | 0 |
| WNS at 100 MHz | +0.684 ns | +0.533 ns | +0.079 ns | +0.050 ns |

: Table 5.5.7: Out-of-context results

The selector check costs RAPIDS 411 LUTs at 8 channels (68,773 on 2026-10-22). At 16 channels
each `scheduler_g` is about 1,630 LUTs against 1,430 for `scheduler`: its window read mux and
base FIFOs in fabric outweigh the run-base generators, whose multipliers are DSPs on the RAPIDS
side; over 32 schedulers that is most of the difference. Both 16-channel builds close 100 MHz,
with the thinner margin (+0.050 ns) the cost of the larger part fill. The register arbiter
(`rapids_g_reg_arb`) is in the top, outside `rapids_core_g`, and not in these numbers. The
2026-10-22 8-channel figures below are the first image's. Per half, `rapids_seq_g` is about 1.95k LUTs (gatling about 1.39k of it); the sink half is
38,693 LUTs against 34,943 for `rapids_snk`, and the source half 37,180 against 32,746 for
`rapids_src`. The 4-hart build measured 76,350 LUTs, 56,645 registers, 69 block RAM tiles and
+0.249 ns: eight harts cost about 600 LUTs and 2k registers, and gatling's own path is no longer
the worst. The worst path of `rapids_core_g` is now in the source half, from a scheduler's source
address (`gen_schedulers[3].u_scheduler/u_core/r_src_addr_reg`) to the AXI read engine's
outstanding counter enable, 20 levels. The 64 DSPs of `rapids_core` are the run-base generators'
index-by-stride multipliers, which the firmware replaces with additions.

In the full Genesys 2 harness of Table 5.5.3, rapids-g-8ch takes 111,738 LUTs (54.8%), 65,246
registers, 58 block RAM tiles and no DSPs and closes 100 MHz at +0.061 ns on the executive image
(110,662 LUTs at +0.072 ns on 2026-10-22); rapids-8ch takes 100,007 LUTs at +0.357 ns (2026-10-22
build).
