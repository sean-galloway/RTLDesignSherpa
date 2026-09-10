# LiteDRAM vs pumice through the SAME harness (2026-09-10)

Same board (Nexys A7-100T, MT47H64M16 x16 DDR2), same operating point (75 MHz
sys / 1:2 / DDR2-300, MR0 = 0x0432: BL4, CL3), same RTL in front of the
controller (`char_engine_block`: chargen_regs, generator arrays, crossbars, bus
meters, latency histograms), same UART bridge and address map, same host
program (`pumice_char` matrix profile, `--char-scale 1000`, one writer + one
reader), same CSV writer. The only difference is the controller behind the
AXI4 port.

Sources: `litedram_2026-09-10_matrix.csv` (this run, timing-clean bitstream,
WNS +0.195 ns) and `board_2026-09-10_burstlen.csv` (pumice `open_page`, the
best pumice preset). Bandwidth is from the hardware first/last stamps of the
engine that ran; latency is the AR-to-first-R histogram mean in MC cycles.
Peak at this point is 600 MB/s.

## Streaming (page-friendly) patterns

| scenario | pumice wr | LiteDRAM wr | pumice rd | LiteDRAM rd | pumice lat | LiteDRAM lat |
|---|---|---|---|---|---|---|
| incremental_bl4 | 551.3 | 554.1 | 290.8 | 564.1 | 49.4 | 24.7 |
| incremental_bl8 | 551.4 | 554.2 | 291.7 | 564.1 | 49.2 | 24.7 |
| incremental_bl16 | 551.3 | 554.2 | 291.7 | 564.1 | 49.3 | 24.8 |
| row_major_bl4 | 570.2 | 569.2 | 290.8 | 579.4 | 49.4 | 24.8 |
| row_major_bl8 | 570.3 | 569.2 | 291.8 | 579.5 | 49.2 | 24.8 |
| row_major_bl16 | 570.3 | 569.3 | 291.8 | 579.5 | 49.2 | 24.7 |

Writes are equal (both ~92-95% of peak). Reads are not: LiteDRAM sustains
94-97% of peak where pumice is pinned at 48.6%, and LiteDRAM's read latency
is half of pumice's.

## Page-thrash patterns

| scenario | pumice wr | LiteDRAM wr | pumice rd | LiteDRAM rd |
|---|---|---|---|---|
| col_major_bl4 | 98.3 | 207.5 | 102.4 | 289.7 |
| col_major_bl8 | 163.8 | 304.0 | 172.0 | 386.3 |
| col_major_bl16 | 262.1 | 396.4 | 237.5 | 463.6 |
| col_major_interleaved_bl4 | 196.6 | 180.2 | 213.0 | 184.3 |
| col_major_interleaved_bl8 | 208.9 | 276.9 | 225.3 | 280.1 |
| col_major_interleaved_bl16 | 311.3 | 376.8 | 273.0 | 380.9 |
| col_major_bl8_multiid | 163.8 | 304.0 | 172.0 | 386.3 |
| col_major_bl8_gap | 163.8 | 300.0 | 172.0 | 300.0 |

LiteDRAM is 1.4-2.8x better on same-bank row thrash. Bank interleave is the
one place pumice leads (bl4 interleaved: 213 vs 184 rd), consistent with
LiteDRAM's per-bank machines not pipelining activates across banks at BL4
(the host summary flags "bank interleave gives no gain over same-bank
thrash" for LiteDRAM at every burst length).

## What this settles

- PUMICE-025's framing ("BL4 at this operating point needs a column every MC
  cycle, so the read ceiling is a property of the operating point") is
  disproven: LiteDRAM at the same BL4 / 75 MHz / 1:2 reads at 579 MB/s
  through identical engines. The 48.6% read ceiling is pumice's.
- It is read-specific and command-path-shaped: pumice's write path already
  matches LiteDRAM, so the DFI/PHY/data path is not the limit. The read side
  loses half its column slots somewhere between AR accept and R return
  (the return ring / rd CAM / AR-order commit are the suspects; PUMICE-025
  already exonerated the generator and the RD data path).
- The 24.7-cycle LiteDRAM read latency is a useful floor: pumice's 49.2 is
  ~25 cycles of extra pipeline for the same DRAM access.

## Area (post-route, xc7a100tcsg324-1, `report_utilization -hierarchical`)

Both bitstreams are timing-clean at 75 MHz (pumice WNS +0.039 ns on 93960
endpoints; LiteDRAM +0.195 ns on 69640).

| whole bitstream | LUTs | FFs | RAMB36 | RAMB18 | DSP |
|---|---|---|---|---|---|
| pumice `ddr2_char_top` | 33579 (53.0%) | 29152 (23.0%) | 2 | 0 | 58 |
| LiteDRAM `litedram_char_top` | 22350 (35.3%) | 21758 (17.2%) | 13 | 9 | 60 |

The shared measurement spine is the same in both, which is the point of the
extraction and a check that the A/B is one measurement path:

| shared block | pumice | LiteDRAM |
|---|---|---|
| `char_engine_block` (generators, crossbars, chargen regs, perf) | 12178 LUT / 13647 FF | 11968 LUT / 13568 FF |
| `bridge_ddr2_char_axil` | 3250 / 2951 | 2664 / 2295 |
| `harness_csr` | 775 / 475 | 649 / 481 |
| `uart_axil_bridge` | 498 / 633 | 498 / 633 |
| debug_sram + dfi_mon_ram | 2215 / 942 | 2170 / 942 |

(The bridge differs because pumice's `ddr2_apb` slave is live and LiteDRAM's
is terminated: 795 LUT of APB converter versus 190.)

Controller side, which is what the comparison is about:

| controller stack | LUTs | FFs | LUTRAM | RAMB36 | DSP |
|---|---|---|---|---|---|
| pumice `pumice_top` (via `pumice_top_geared`, gearing bypassed) | 12224 | 7878 | 300 | 2 | 2 |
| + `a7ddrphy` | 421 | 509 | 0 | 0 | 0 |
| + `dfi_cmd_delay` / `dfi_rddata_delay` shims | 336 | 1280 | 0 | 0 | 0 |
| **pumice total** | **12981** | **9667** | 300 | 2 | 2 |
| LiteDRAM `litedram_core` leaf (controller + a7ddrphy + CSR + PLL) | 2411 | 2046 | 231 | 12 | 0 |
| + `VexRiscv` BIOS CPU (init/levelling; pumice does this from the host) | 1925 | 1279 | 0 | 1 | 4 |
| **`litedram_core` total** | **4335** | **3325** | 231 | 13 | 4 |

So pumice's controller stack is **5.4x the LUTs and 4.7x the flops** of
LiteDRAM's controller+PHY, and 3.0x / 2.9x even against the whole
`litedram_core` including a RISC-V CPU that pumice does not need. It delivers
half the read bandwidth and twice the read latency at the same operating
point.

Caveats on the split. LiteX emits `litedram_core` as one flat Verilog module,
so its 2411 LUT leaf row cannot be divided further: that number contains the
DDR2 controller, the a7ddrphy, the wishbone/CSR fabric and the clock
generator, and is therefore an **upper bound** on its controller alone.
Pumice's 12224 is the controller alone, with its CSR block but without PHY or
DFI shims. The two are not the same microarchitecture -- pumice carries
reorder CAMs (2 RAMB36 + 300 LUTRAM), an AR-order read return ring, runtime
paging/scheduling/refresh modes and a width-gearing wrapper, where LiteDRAM
runs per-bank FSMs with round-robin arbitration and no reordering. Some of
pumice's area buys configurability the comparison does not exercise. None of
it currently buys bandwidth.

## Refactor is behaviour-neutral on silicon

The shared `char_engine_block` was extracted from `ddr2_char_macro` for this
comparison, so the pumice board build was re-run on the refactored source and
re-characterized. Timing: WNS +0.039 ns, 0 failing of 93960 endpoints. Board:
all 14 `open_page` scenarios integrity-clean, and against the pre-refactor
run (`board_2026-09-10_burstlen.csv`) the largest difference is 0.08 MB/s on
writes and 0.01 MB/s on reads. The extraction changed nothing measurable.

## Method notes

- One writer, one reader (generator 0) on both sides; the multi-writer
  bank_parallel scenario is excluded until PUMICE-027 (B out of AW order vs
  the position-routed write bridge) is resolved.
- LiteDRAM has no runtime knobs; its "config" is what `litedram_hp.yml`
  generated (ROW_BANK_COL, open page with lookahead auto-precharge,
  cmd_buffer_depth 16). pumice numbers are its `open_page` preset (FR-FCFS,
  row-major, open page), the best of its matrix.
- LiteDRAM utilisation columns are meter-window artefacts at this run size,
  as the host notes; bandwidth is stamp-based and unaffected.
- Repro: `make -C projects/fpga-systems/NexysA7/pumice/ddr2-characterization/flows-litedram-uart program`
  then `make ... host-litedram_char ARGS="--char-profile matrix --char-scale 1000 --csv <path>"`.
