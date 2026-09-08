# DDR2/LPDDR2 Memory Controller — Nexys A7 Characterization

**Status:** Skeleton — directories scaffolded, harness RTL not yet written
**Target board:** Digilent Nexys A7-100T (Artix-7 XC7A100T-CSG324)
**Target DRAM:** Onboard Micron `MT47H64M16HR-25E` (DDR2, 16-bit, single-rank, 800 Mbps, 128 MiB)
**Component under test:** [`projects/components/memory-controllers/pumice-ddr2-lpddr2/`](../../components/memory-controllers/pumice-ddr2-lpddr2/)

---

## Purpose

End-to-end characterization of the DDR2/LPDDR2 family memory controller on real silicon. The controller is co-developed in `projects/components/memory-controllers/pumice-ddr2-lpddr2/` (RTL + DV + HAS + MAS) and validated in sim against the DFI BFM in the DV repo. This project drives **board-level workloads** through the controller against the real Micron device and reports throughput / latency / data integrity per workload mix.

Hardware characterization lives in `projects/NexysA7/` rather than in the component tree to preserve the component-as-IP-block boundary.

This is the **DDR2 sibling of `stream_characterization/`** — same shape, different DUT.

---

## Validation Methodology

DFI v2.1 is the canonical interface between our controller and the DRAM PHY. The PHY itself (FPGA IOB serdes, OSERDESE2/ISERDESE2 tap calibration, IDELAY training) is FPGA-specific and out of scope for our family controllers. For Nexys A7 we reuse **LiteDRAM's `a7ddrphy`** verbatim and drive its DFI master port from our controller.

```
  ┌───────────────────────────────────────────────────────┐
  │ char harness (this project)                            │
  │                                                        │
  │   axi4_master_wr_pat_gen  ──┐                          │
  │   (strided addr + LFSR)     │                          │
  │                             ▼   AXI4                   │
  │                          ┌─────┐                       │
  │                          │s_axi│ ► our DDR2 controller ► a7ddrphy ► MT47H64M16
  │                          └─────┘   DFI v2.1              IOB
  │                             ▲                          │
  │   axi4_master_rd_crc_chk  ──┘                          │
  │   (strided addr + CRC)                                 │
  │                                                        │
  │   harness_csr / bus meter + latency hist / leds / 7-seg│
  └────────────────────────────────────────────────────────┘
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
└── build-perf/                         our DDR2 controller + UART-driven host
    ├── rtl/                                 char top + harness + a7ddrphy binding
    ├── tcl/                                 (TODO) Vivado build scripts
    ├── constraints/                         Nexys A7 XDC (board pins done, DDR2 TODO)
    ├── dv/                                  (TODO) cocotb sim of the harness
    ├── host/                                (TODO) Python driver against harness_csr
    ├── csv/                                 (TODO) committed sweep output
    ├── plots/                               (TODO) committed plots
    ├── reports/                             (TODO) Vivado timing/util
    ├── bitstream/                           (TODO) known-good bitstreams
    └── README.md                            (TODO) per-flow doc
```

A future `flows-litedram-uart/` sibling (LiteDRAM controller + same UART harness) lands later as the baseline comparison cell. **No CPU in the FPGA build:** the Nexys A7 100T doesn't have the LUT budget to fit our DDR2 controller + perf logic + a soft CPU. The host drives the harness over UART from an off-board machine.

---

## Harness Architecture — what we need to build

The harness mirrors `stream_characterization`'s pattern of "generate, drive, check, report", flipped for the DDR2 case (data goes **out** to memory, comes **back**, and gets CRC'd here on the master side instead of the slave side).

| Block | Source | Notes |
|-------|--------|-------|
| `axi4_master_wr_pattern_gen` | `rtl/amba/shared/` | Master-side LFSR pattern-gen with a built-in 2D strided address generator (stride_0/1 + wrap_mask_0/1). Emits AW + `wdata` seeded by burst index; catches BRESP errors. |
| `axi4_master_rd_crc_check` | `rtl/amba/shared/` | Master-side CRC accumulator with its own strided address generator (mirrors the writer). Reads back and CRCs the returned `rdata` against the LFSR-computed expected value; flags mismatches. |
| `dataint_crc` | `rtl/common/dataint_crc.sv` | **Reuse as-is.** Same CRC primitive both engines instantiate. |
| `harness_csr` | this project (`ddr2_char_framework/rtl/harness_csr.sv`) | AXIL slave. Holds every engine cfg reg (0x100/0x180 blocks), the characterization timer, the perf-observability readback (0x1C0..0x1E8), and the bring-up ctrl/status pulses. |
| `axi_bus_meter`, `axi_perf_latency_hist` | `rtl/amba/shared/` | Instantiated inside `ddr2_char_macro`, tapped on the internal AXI wires between the engines and the controller's s_axi port. WR side: W meter + AW→B histogram. RD side: R meter + AR→firstR/RLAST histograms. |
| `axi_response_delay` | `ddr2_char_framework/rtl/axi_response_delay.sv` (from stream) | Committed to the framework but not yet instantiated. `harness_csr.o_rd_resp_delay_cyc/o_wr_resp_delay_cyc` are the future knobs. |
| `led_status_driver`, `seven_seg_4digit` | `ddr2_char_framework/rtl/` (from stream) | **Reuse as-is.** Live status display. |

---

## Phased Validation Plan

| Phase | What | Location | Status |
|-------|------|----------|--------|
| 1 | cocotb sim with DDR2 DFI BFM | `RTLDesignSherpa-DV` | Done (80.2 % top-only coverage, 100 % FUB) |
| 2 | cocotb sim with LiteDRAM's Verilog DDR2 model (co-sim) | `RTLDesignSherpa-DV` | Blocked on LiteX cocktail + phase-mismatch — see memory `project_litedram_cosim_blockers.md`; ~1.5–2 days work |
| 3 | Nexys A7 hardware bring-up — UART-driven host walks the pattern-gen / CRC-check pair against real DDR2 | this directory | Future |
| 4 | Workload characterization with this harness — pattern + CRC sweeps + perf counters → CSV → plots | this directory | Skeleton (directory + plan only) |

Phase 4 is what `build-perf/` runs. The two pattern-gen engines share the controller's `s_axi` port; each has its own strided address generator programmed through `harness_csr` cfg regs (linear / 2D row-major / wrap / reverse via stride + wrap-mask fields). The CRC-check pair verifies data integrity end-to-end, and the AXI bus meters + latency histograms tapped inside `ddr2_char_macro` measure throughput / latency. CSVs land under `build-perf/csv/`; plots under `plots/`.

Extended-endurance work (24-hour soak, thermal chamber) fits inside Phase 3/4 — no OS is running so the "real OS access patterns" story from the earlier VexRiscv plan is off the table on this board. If we want that, it moves to a bigger FPGA target that can host both our controller and Linux.

---

## Resource Budget (XC7A100T — 63,400 LUTs available)

| Block | Est. LUTs | Notes |
|-------|----------|-------|
| Our DDR2 controller | ~12,000 | Controller only; no PHY. Per HAS §2.1 target envelope. |
| `a7ddrphy` (LiteDRAM PHY) | ~2,000 | FPGA-specific IOB serdes. Reused from LiteDRAM. |
| Char engines (WR pattern-gen + RD CRC-check, each with its own strided address gen) | ~2,000 | LFSR + CRC + built-in stride/wrap gen |
| Perf logic (`axi_bus_meter` + `axi_perf_latency_hist` x WR+RD, `harness_csr`, debug_sram, dfi_mon_ram) | ~3,000 | Grows with meter counters + histogram bins |
| 1×5 AXIL bridge (host→APB/CSR/SRAMs) | ~1,500 | Generated `bridge_ddr2_char_axil` |
| UART↔AXIL bridge + LED/7-seg | ~1,000 | UART FSM + display drivers |
| **Total** | **~21,500 / 63,400 (~34 %)** | No CPU on this board — the 100T doesn't have the budget for DDR2 + perf + a soft CPU together; host drives over UART |

Multi-rank (`NUM_RANKS ∈ {1, 2, 4}`) is not exercised on this board — the onboard DDR2 is single-rank by construction. Multi-rank validation happens later on a DDR3/4 board with a multi-rank DIMM socket.

---

## Recommended Stack

- **CPU:** none on the FPGA. The Nexys A7 100T can't fit our DDR2 controller + perf logic + a soft CPU with any timing margin. The host runs on an off-board machine and drives the harness over the FTDI UART. (VexRiscv + LiteX was the earlier plan; dropped after the CPU-vs-perf budget shookout.)
- **Host:** Python driver against `harness_csr`'s register map, hitting the AXIL slaves through the UART→AXIL bridge (see `build-perf/host/`, TBD).
- **Init UART:** the FTDI UART path under `projects/NexysA7/` is the entry point — same wiring as `stream_characterization` and `timing_characterization`.

---

## Cross-References

- HAS: `projects/components/memory-controllers/pumice-ddr2-lpddr2/docs/DDR2_LPDDR2_HAS_v0.5.pdf`
- MAS: `projects/components/memory-controllers/pumice-ddr2-lpddr2/docs/DDR2_LPDDR2_MAS_v0.5.pdf`
- Controller RTL home: `projects/components/memory-controllers/pumice-ddr2-lpddr2/rtl/`
- DFI BFM (DV side): `RTLDesignSherpa-DV/src/CocoTBFramework/components/dfi/` — released as `cocotb-framework==0.3.0`
- Sibling characterization projects: `projects/NexysA7/stream_characterization/`, `projects/NexysA7/timing_characterization/`
- Stream harness blocks we're adapting on the master side: `rtl/amba/shared/axi4_slave_rd_pattern_gen.sv`, `rtl/amba/shared/axi4_slave_wr_crc_check.sv`, `rtl/amba/shared/axi4_dma_slaves.sv`
- Address generator: `projects/components/misc/rtl/dma_address_gen.sv`
- LiteX upstream: https://github.com/enjoy-digital/litex
- LiteDRAM upstream (for the `a7ddrphy` we'll consume): https://github.com/enjoy-digital/litedram

---

## Decision Log

- **2026-06-15** — Original DDR2 bring-up plan recorded under `projects/NexysA7/pumice-memory-controller/`. Validation methodology (DFI controller + LiteDRAM `a7ddrphy`), CPU choice (VexRiscv Linux on LiteX), and three-sub-phase hardware bring-up agreed. Resource budget fits comfortably (~36 % LUTs). No work started yet — DDR2 controller pre-RTL (HAS v0.2 + MAS v0.1 skeleton).
- **2026-06-25** — Directory renamed `pumice-memory-controller/` → `ddr2-characterization/` to align with the `stream_characterization/` sibling and reflect the workload-characterization focus. Harness architecture recorded: reuse `dma_address_gen` + the stream `dataint_crc` + `axi_response_delay` + `harness_csr` + LED/7-seg drivers; author **two new master-side blocks** — `axi4_master_wr_pattern_gen` and `axi4_master_rd_crc_check` — by adapting stream's slave-side `axi4_slave_rd_pattern_gen` + `axi4_slave_wr_crc_check`. Initial flow: `flows-ours-vex/` only; `flows-litedram-vex/` lands later as baseline comparison.
- **2026-07-04** — Bridge shrunk from 1×5 to 1×4: dropped `desc_ram`. The pattern-gen engines already have strided address generators built in (driven by `stride_0/1` + `wrap_mask_0/1` cfg regs at 0x100/0x180), so the descriptor-mode workload path the earlier plan reserved `desc_ram` for is redundant. If we later want a scripted / trace-replay workload class the engines can't express, re-add a fresh slave with the right shape rather than trying to repurpose a placeholder.
- **2026-07-03** — Drop the soft-CPU story from the Nexys A7 target. XC7A100T doesn't have the LUT budget to fit our DDR2 controller + perf logic + VexRiscv+LiteX simultaneously with any timing margin. Flow renamed `flows-ours-vex/` → `build-perf/`; the host machine drives the harness through the FTDI UART instead. Resource budget rewritten around perf logic (`axi_bus_meter` + `axi_perf_latency_hist` on WR+RD, tapped inside `ddr2_char_macro`). Future flows follow the same naming: `flows-<controller>-uart/` for the on-Nexys builds; `flows-<controller>-vex/` reserved for larger FPGA targets where a CPU actually fits.
