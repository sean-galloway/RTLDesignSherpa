# DDR2/LPDDR2 Memory Controller — Nexys A7 Hardware Bring-Up

**Status:** Planning — not yet started
**Target board:** Digilent Nexys A7-100T (Artix-7 XC7A100T-CSG324)
**Target DRAM:** Onboard Micron `MT47H64M16HR-25E` (DDR2, 16-bit, single-rank, 800 Mbps, 128 MiB)
**Component under test:** [`projects/components/memory-controllers/ddr2-lpddr2/`](../../components/memory-controllers/ddr2-lpddr2/)

---

## Purpose

This directory holds the FPGA hardware bring-up project for validating the DDR2/LPDDR2 family memory controller on real silicon. The controller is co-developed in `projects/components/memory-controllers/ddr2-lpddr2/` (RTL + DV + HAS + MAS); this project is the **board-level integration** that proves the controller works end-to-end against a real DRAM device under a real CPU's access pattern.

Hardware bring-up lives in `projects/NexysA7/` rather than in the component tree to preserve the component-as-IP-block boundary.

---

## Validation Methodology

DFI v2.1 is the canonical interface between our controller and the DRAM PHY. The PHY itself — FPGA IOB serdes, OSERDESE2/ISERDESE2 tap calibration, IDELAY training — is FPGA-specific and out of scope for our family controllers. For Nexys A7 bring-up we reuse **LiteDRAM's `a7ddrphy`** verbatim and drive its DFI master port from our controller.

```
  ┌─────────────────────────┐  AXI4   ┌──────────────────────┐  DFI v2.1  ┌─────────────┐  IOB  ┌──────────┐
  │ VexRiscv-Linux (LiteX)  │ ──────► │ Our DDR2 controller  │ ──────────► │  a7ddrphy   │ ────► │ MT47H64  │
  └─────────────────────────┘         │ (the component)      │             │ (LiteDRAM)  │       │ (onboard)│
                                      └──────────────────────┘             └─────────────┘       └──────────┘
```

The boundary at DFI is the same boundary the DV repo's BFM uses. Code that passes in cocotb against the BFM should pass on hardware against the a7ddrphy, modulo PHY-side training quirks.

---

## Resource Budget (XC7A100T — 63,400 LUTs available)

| Block                                                 | Est. LUTs | Notes                                                            |
|-------------------------------------------------------|-----------|------------------------------------------------------------------|
| Our DDR2 controller                                   | ~12,000   | Controller only; no PHY. Per HAS §2.1 target envelope.           |
| `a7ddrphy` (LiteDRAM PHY)                             | ~2,000    | FPGA-specific IOB serdes. Reused from LiteDRAM.                  |
| VexRiscv (Linux config, MMU + Icache + Dcache)        | ~5,000    | RV32IMA, boots mainline Linux                                    |
| LiteX SoC fabric (Wishbone + AXI bridge, UART, GPIO)  | ~3,000    | "Boring infrastructure"                                          |
| Misc glue (UART init path, JTAG hooks)                | ~1,000    |                                                                  |
| **Total**                                             | **~23,000 / 63,400 (~36%)** | Comfortable; BRAM ~40% for Linux boot ROM + caches |

Multi-rank (`NUM_RANKS ∈ {1, 2, 4}`) is not exercised on this board — the onboard DDR2 is single-rank by construction. Multi-rank validation happens later on a DDR3/4 board with a multi-rank DIMM socket.

---

## Recommended Stack

- **CPU:** VexRiscv, Linux config (MMU + caches). Mature LiteX integration, ~5K LUTs, boots mainline Linux. Alternatives: PicoRV32 / NEORV32 for stress-test-only sub-phases (no MMU → no Linux, but ~2K LUTs).
- **SoC framework:** LiteX. Already has a Nexys A7 board target, VexRiscv-Linux target, `a7ddrphy`, and DFI plumbing. Use LiteX for everything except the DDR controller — swap LiteDRAM's controller out for ours, keep its PHY.
- **Init UART:** the existing UART path under `projects/NexysA7/` is the entry point; same wiring as `stream_characterization` and `timing_characterization`.

---

## Phased Validation Plan

| Phase | What                                                            | Location                                          | Status      |
|-------|-----------------------------------------------------------------|---------------------------------------------------|-------------|
| 1     | cocotb sim with DDR2 DFI BFM                                    | `RTLDesignSherpa-DV` (DV repo)                    | Planned     |
| 2     | cocotb sim with LiteDRAM's Verilog DDR2 model (co-sim)          | `RTLDesignSherpa-DV` (DV repo)                    | Blocked on LiteX version cocktail + phase-mismatch (see memory `project_litedram_cosim_blockers.md`); ~1.5–2 days work |
| 3a    | Nexys A7 hardware, **VexRiscv barebones**, memtester from BRAM  | this directory                                    | Future      |
| 3b    | Nexys A7 hardware, **VexRiscv Linux**, kernel memtester + stress-ng from SD card | this directory                  | Future      |
| 3c    | Extended endurance (24-hour memtester, thermal soak)            | this directory                                    | Future      |

Phase 3b is the strongest evidence short of ASIC tapeout: real OS access patterns (refresh-while-DMA, mixed read/write at random offsets, page-table walks, kmalloc/kfree thrash) running against our DDR2 controller for hours at a time.

---

## Directory Layout (when work begins)

```
projects/NexysA7/ddr2-lpddr2-memory-controller/
├── README.md                       # this file
├── litex/
│   ├── nexys_a7_ddr2.py            # LiteX board target with our DDR2 controller
│   ├── soc.py                      # SoC integration (CPU + fabric + DDR + UART)
│   └── filelists/                  # SV/Verilog filelists for our controller
├── sw/
│   ├── bootloader/                 # BRAM-resident bootloader (Phase 3a)
│   ├── memtester/                  # standalone memtester (Phase 3a)
│   └── linux/
│       ├── buildroot-config        # Buildroot config for the Linux image
│       ├── dts/                    # device tree source
│       └── stress-scripts/         # Phase 3b/3c stress-test scripts
├── bitstreams/                     # checked-in known-good bitstreams (small, infrequent)
├── reports/                        # Vivado timing/utilization reports
└── notes/                          # bring-up logs, scope captures, JTAG sessions
```

---

## Cross-References

- HAS: `projects/components/memory-controllers/ddr2-lpddr2/docs/DDR2_LPDDR2_HAS_v0.2.pdf`
- MAS: `projects/components/memory-controllers/ddr2-lpddr2/docs/DDR2_LPDDR2_MAS_v0.1.pdf`
- Controller RTL home: `projects/components/memory-controllers/ddr2-lpddr2/rtl/`
- DFI BFM (DV side): `RTLDesignSherpa-DV/src/CocoTBFramework/components/dfi/`
- Sibling bring-up projects (for layout reference): `projects/NexysA7/stream_characterization/`, `projects/NexysA7/timing_characterization/`
- LiteX upstream: https://github.com/enjoy-digital/litex
- LiteDRAM upstream (for the `a7ddrphy` we'll consume): https://github.com/enjoy-digital/litedram

---

## Decision Log

- **2026-06-15** — Plan recorded. Validation methodology (DFI controller + LiteDRAM `a7ddrphy`), CPU choice (VexRiscv Linux on LiteX), and three-sub-phase hardware bring-up agreed. Resource budget fits comfortably (~36% LUTs on XC7A100T). No work started yet — DDR2 controller is still pre-RTL (HAS v0.2 + MAS v0.1 skeleton).
