# DDR2/LPDDR2 Memory Controller — Nexys A7 Characterization

**Status:** Skeleton — directories scaffolded, harness RTL not yet written
**Target board:** Digilent Nexys A7-100T (Artix-7 XC7A100T-CSG324)
**Target DRAM:** Onboard Micron `MT47H64M16HR-25E` (DDR2, 16-bit, single-rank, 800 Mbps, 128 MiB)
**Component under test:** [`projects/components/memory-controllers/ddr2-lpddr2/`](../../components/memory-controllers/ddr2-lpddr2/)

---

## Purpose

End-to-end characterization of the DDR2/LPDDR2 family memory controller on real silicon. The controller is co-developed in `projects/components/memory-controllers/ddr2-lpddr2/` (RTL + DV + HAS + MAS) and validated in sim against the DFI BFM in the DV repo. This project drives **board-level workloads** through the controller against the real Micron device and reports throughput / latency / data integrity per workload mix.

Hardware characterization lives in `projects/NexysA7/` rather than in the component tree to preserve the component-as-IP-block boundary.

This is the **DDR2 sibling of `stream_characterization/`** — same shape, different DUT.

---

## Validation Methodology

DFI v2.1 is the canonical interface between our controller and the DRAM PHY. The PHY itself (FPGA IOB serdes, OSERDESE2/ISERDESE2 tap calibration, IDELAY training) is FPGA-specific and out of scope for our family controllers. For Nexys A7 we reuse **LiteDRAM's `a7ddrphy`** verbatim and drive its DFI master port from our controller.

```
  ┌─────────────────────────────────────────────────┐
  │ char harness (this project)                      │
  │                                                  │
  │   dma_address_gen ──► axi4_master_wr_pat_gen ──┐ │
  │   (algo mix)         (LFSR-seeded by addr)     │ │
  │                                                ▼ │  AXI4
  │   dma_address_gen ──► axi4_master_rd_crc_chk ◄─┤ ◄─────► our DDR2 controller ──► a7ddrphy ──► MT47H64M16
  │   (same mix)         (CRC vs expected)         │ │  DFI v2.1          IOB
  │                                                ▼ │
  │   harness_csr / leds / 7-seg / perf counters     │
  └──────────────────────────────────────────────────┘
```

The boundary at DFI is the same boundary the DV repo's BFM uses. Code that passes in cocotb against the BFM should pass on hardware against the `a7ddrphy`, modulo PHY-side training quirks.

---

## Layout

```
ddr2-characterization/                       ← this directory (umbrella)
│
├── README.md                                this file
├── Makefile                                 (TODO) orchestrates all flows
│
├── docs/                                    shared characterization writeup
│   └── (TBD: assets/, characterization findings, methodology notes)
│
├── ddr2_char_framework/                     shared instrumentation
│   ├── rtl/                                 (TODO) harness CSR, perf counters,
│   │                                          LEDs / 7-seg, address-gen wrapper,
│   │                                          axi4_master_wr_pattern_gen,
│   │                                          axi4_master_rd_crc_check
│   └── host/                                (TODO) plot_results.py, sweep
│                                              runners, CSV ingest
│
└── flows-ours-vex/                          our DDR2 controller + VexRiscv-Linux
    ├── rtl/                                 (TODO) char top + LiteX SoC integration
    ├── tcl/                                 (TODO) Vivado build scripts
    ├── constraints/                         (TODO) Nexys A7 XDC + clock + I/O
    ├── dv/                                  (TODO) cocotb sim of the harness
    ├── host/                                (TODO) sweep + plot CSV
    ├── csv/                                 (TODO) committed sweep output
    ├── plots/                               (TODO) committed plots
    ├── reports/                             (TODO) Vivado timing/util
    ├── bitstream/                           (TODO) known-good bitstreams
    └── README.md                            (TODO) per-flow doc
```

A future `flows-litedram-vex/` sibling (LiteDRAM controller + same VexRiscv-Linux harness) lands later as the baseline comparison cell.

---

## Harness Architecture — what we need to build

The harness mirrors `stream_characterization`'s pattern of "generate, drive, check, report", flipped for the DDR2 case (data goes **out** to memory, comes **back**, and gets CRC'd here on the master side instead of the slave side).

| Block | Source | Notes |
|-------|--------|-------|
| `dma_address_gen` | `projects/components/misc/rtl/dma_address_gen.sv` | **Reuse as-is.** 2D strided generator with wrap + signed strides. Drives AW + AR addresses through descriptor programming (linear / 2D row-major / wrap region / reverse). |
| `axi4_master_wr_pattern_gen` (**new**) | adapted from `axi4_slave_rd_pattern_gen` (stream) | Master-side LFSR pattern-gen that emits `wdata` seeded by `awaddr`. Consumes addresses from `dma_address_gen`, wraps `axi4_master_wr` for the AW/W/B protocol. |
| `axi4_master_rd_crc_check` (**new**) | adapted from `axi4_slave_wr_crc_check` (stream) | Master-side CRC accumulator that reads back from the same addresses and CRCs the returned `rdata` against the expected CRC computed from the same LFSR + addresses. Compare-on-completion mismatch → harness latches an error. |
| `dataint_crc` | `rtl/common/dataint_crc.sv` | **Reuse as-is.** Same CRC primitive both stream-side blocks instantiate. |
| `harness_csr` | adapted from `stream_char_framework/rtl/harness_csr.sv` | Holds workload program (descriptor), result counters (latency, throughput, CRC mismatch), and soft-reset hooks. |
| `axi_response_delay` | `stream_char_framework/rtl/axi_response_delay.sv` | **Reuse as-is.** Per-channel R/B response delay queues for stress-testing the controller under back-pressure. |
| `led_status_driver`, `seven_seg_4digit` | `stream_char_framework/rtl/` | **Reuse as-is.** Live status display. |

The two new blocks (`axi4_master_wr_pattern_gen`, `axi4_master_rd_crc_check`) are the work item.

---

## Phased Validation Plan

| Phase | What | Location | Status |
|-------|------|----------|--------|
| 1 | cocotb sim with DDR2 DFI BFM | `RTLDesignSherpa-DV` | Done (80.2 % top-only coverage, 100 % FUB) |
| 2 | cocotb sim with LiteDRAM's Verilog DDR2 model (co-sim) | `RTLDesignSherpa-DV` | Blocked on LiteX cocktail + phase-mismatch — see memory `project_litedram_cosim_blockers.md`; ~1.5–2 days work |
| 3a | Nexys A7 hardware, VexRiscv barebones + memtester from BRAM | this directory | Future |
| 3b | Nexys A7 hardware, VexRiscv Linux + kernel memtester + stress-ng from SD | this directory | Future |
| 3c | Extended endurance (24-hour memtester, thermal soak) | this directory | Future |
| 4 | Workload characterization with this harness — pattern + CRC sweeps + perf counters → CSV → plots | this directory | Skeleton (directory + plan only) |

Phase 4 is what `flows-ours-vex/` runs. The harness uses `dma_address_gen` to walk a descriptor-programmed access pattern, the pattern-gen / CRC-check pair to verify data integrity end-to-end, and the perf counters to measure latency / throughput. CSVs land under `flows-ours-vex/csv/`; plots under `plots/`.

Phase 3b remains the strongest evidence short of ASIC tapeout — real OS access patterns (refresh-while-DMA, mixed read/write at random offsets, page-table walks, kmalloc/kfree thrash) running for hours. The dedicated workload harness in Phase 4 gives reproducible, descriptor-controlled measurements alongside the Linux soak.

---

## Resource Budget (XC7A100T — 63,400 LUTs available)

| Block | Est. LUTs | Notes |
|-------|----------|-------|
| Our DDR2 controller | ~12,000 | Controller only; no PHY. Per HAS §2.1 target envelope. |
| `a7ddrphy` (LiteDRAM PHY) | ~2,000 | FPGA-specific IOB serdes. Reused from LiteDRAM. |
| VexRiscv (Linux config, MMU + Icache + Dcache) | ~5,000 | RV32IMA, boots mainline Linux |
| LiteX SoC fabric (Wishbone + AXI bridge, UART, GPIO) | ~3,000 | "Boring infrastructure" |
| Char harness (pattern/CRC + address gen + CSRs + counters) | ~2,000 | Conservative; the LFSR + CRC are tiny |
| Misc glue (UART init path, JTAG hooks) | ~1,000 | |
| **Total** | **~25,000 / 63,400 (~39 %)** | Comfortable; BRAM ~40 % for Linux boot ROM + caches + descriptor RAM |

Multi-rank (`NUM_RANKS ∈ {1, 2, 4}`) is not exercised on this board — the onboard DDR2 is single-rank by construction. Multi-rank validation happens later on a DDR3/4 board with a multi-rank DIMM socket.

---

## Recommended Stack

- **CPU:** VexRiscv, Linux config (MMU + caches). Mature LiteX integration, ~5K LUTs, boots mainline Linux. Alternatives: PicoRV32 / NEORV32 for stress-test-only sub-phases (no MMU → no Linux, but ~2K LUTs).
- **SoC framework:** LiteX. Already has a Nexys A7 board target, VexRiscv-Linux target, `a7ddrphy`, and DFI plumbing. Use LiteX for everything except the DDR controller — swap LiteDRAM's controller out for ours, keep its PHY.
- **Init UART:** the existing UART path under `projects/NexysA7/` is the entry point; same wiring as `stream_characterization` and `timing_characterization`.

---

## Cross-References

- HAS: `projects/components/memory-controllers/ddr2-lpddr2/docs/DDR2_LPDDR2_HAS_v0.2.pdf`
- MAS: `projects/components/memory-controllers/ddr2-lpddr2/docs/DDR2_LPDDR2_MAS_v0.1.pdf`
- Controller RTL home: `projects/components/memory-controllers/ddr2-lpddr2/rtl/`
- DFI BFM (DV side): `RTLDesignSherpa-DV/src/CocoTBFramework/components/dfi/` — released as `cocotb-framework==0.3.0`
- Sibling characterization projects: `projects/NexysA7/stream_characterization/`, `projects/NexysA7/timing_characterization/`
- Stream harness blocks we're adapting on the master side: `rtl/amba/shared/axi4_slave_rd_pattern_gen.sv`, `rtl/amba/shared/axi4_slave_wr_crc_check.sv`, `rtl/amba/shared/axi4_dma_slaves.sv`
- Address generator: `projects/components/misc/rtl/dma_address_gen.sv`
- LiteX upstream: https://github.com/enjoy-digital/litex
- LiteDRAM upstream (for the `a7ddrphy` we'll consume): https://github.com/enjoy-digital/litedram

---

## Decision Log

- **2026-06-15** — Original DDR2 bring-up plan recorded under `projects/NexysA7/ddr2-lpddr2-memory-controller/`. Validation methodology (DFI controller + LiteDRAM `a7ddrphy`), CPU choice (VexRiscv Linux on LiteX), and three-sub-phase hardware bring-up agreed. Resource budget fits comfortably (~36 % LUTs). No work started yet — DDR2 controller pre-RTL (HAS v0.2 + MAS v0.1 skeleton).
- **2026-06-25** — Directory renamed `ddr2-lpddr2-memory-controller/` → `ddr2-characterization/` to align with the `stream_characterization/` sibling and reflect the workload-characterization focus. Harness architecture recorded: reuse `dma_address_gen` + the stream `dataint_crc` + `axi_response_delay` + `harness_csr` + LED/7-seg drivers; author **two new master-side blocks** — `axi4_master_wr_pattern_gen` and `axi4_master_rd_crc_check` — by adapting stream's slave-side `axi4_slave_rd_pattern_gen` + `axi4_slave_wr_crc_check`. Initial flow: `flows-ours-vex/` only; `flows-litedram-vex/` lands later as baseline comparison.
