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

# RTL Design Sherpa - Production Components Index

**Last Updated:** 2026-10-12

---

## Overview

This directory contains production-ready and in-development component projects for RTL Design Sherpa. Each component has complete documentation, verification, and integration support.

**For detailed component documentation**, see [docs/markdown/projects/index.md](../../docs/markdown/projects/index.md)

---

## Component List

| Component | Status | Location | Documentation |
|-----------|--------|----------|---------------|
| **Retro Legacy Blocks (HPET, PIT, ...)** | Production | [retro_legacy_blocks/](retro_legacy_blocks/) | [HPET Specification](retro_legacy_blocks/docs/hpet_mas/hpet_mas_index.md) |
| **APB Crossbar** | Production | [fabric-gen-ip/apbx-xbar/](fabric-gen-ip/apbx-xbar/) | [HAS](fabric-gen-ip/apbx-xbar/docs/apbx_xbar_has/apbx_xbar_has_index.md) · [MAS](fabric-gen-ip/apbx-xbar/docs/apbx_xbar_mas/apbx_xbar_mas_index.md) · [GAS](fabric-gen-ip/apbx-xbar/docs/apbx_xbar_gas/apbx_xbar_gas_index.md) |
| **STREAM** | Production | [dma-ip/stream/](dma-ip/stream/) | [Specification](dma-ip/stream/docs/stream_mas/stream_index.md) |
| **RAPIDS** | Production (owner-confirmed Done 2026-10-11) | [dma-ip/rapids/](dma-ip/rapids/) | [Specification](dma-ip/rapids/docs/rapids_beats_mas/rapids_beats_mas_index.md) |
| **Bridge** | Production (Done 2026-10-11) | [fabric-gen-ip/bridge/](fabric-gen-ip/bridge/) | [HAS](fabric-gen-ip/bridge/docs/bridge_has/bridge_has_index.md) · [MAS](fabric-gen-ip/bridge/docs/bridge_mas/bridge_mas_index.md) · [GAS](fabric-gen-ip/bridge/docs/bridge_gas/bridge_gas_index.md) |
| **Delta** | Active — AXI-Stream crossbar generator (RTL generated; DV suite TODO); re-homed from noc-ip 2026-10-12 | [fabric-gen-ip/delta/](fabric-gen-ip/delta/) | [PRD](fabric-gen-ip/delta/PRD.md), [GAS](fabric-gen-ip/delta/docs/delta_gas/delta_gas_index.md), [NoC draft spec](noc-ip/delta_spec/delta_index.md) |
| **Converters** | Production | [utility-ip/converters/](utility-ip/converters/) | See [utility-ip/converters/docs/](utility-ip/converters/docs/) |
| **misc** | Production | [utility-ip/misc/](utility-ip/misc/) | [README](utility-ip/misc/README.md) |
| **pumice (DDR2/LPDDR2 memory controller)** | Production (at rest; board-validated Nexys A7) | [mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/](mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/) | [Specification](mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/docs/pumice_mas/pumice_mas_index.md) |
| **scoria (DDR3/LPDDR3 memory controller)** | In progress — simulation-verified (221 tests, 9 formal blocks); board campaign is the qualifier | [mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/](mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/) | [HAS](mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/docs/) |
| **andesite (DDR4/LPDDR4 memory controller)** | Planned — directory baseline, structure only | [mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/](mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/) | [README](mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/README.md) |
| **granite / gabbro / diorite (product tops)** | Scaffold 2026-10-11 — granite active under wrapper-dissolution TASK-001; gabbro/diorite placeholders | [mem-ctrl-ip/product-ip/](mem-ctrl-ip/product-ip/) | [README](mem-ctrl-ip/product-ip/README.md) |
| **ecc-ip / Reed-Solomon** | Production — 1.0, Genesys-2 board-validated | [ecc-ip/reed-solomon/](ecc-ip/reed-solomon/) | [family README](ecc-ip/README.md), [PRD](ecc-ip/reed-solomon/PRD.md), [References](ecc-ip/reed-solomon/References/README.md) |
| **ecc-ip / BCH** | Production — 1.0, Genesys-2 board-validated | [ecc-ip/bch/](ecc-ip/bch/) | [README](ecc-ip/bch/README.md) |
| **kestrel (RV32I single-cycle core)** | Production — rv32ui 42/42 spike lockstep, riscv-formal 42/42 | [riscv-ip/kestrel-rv32i/](riscv-ip/kestrel-rv32i/) | [HAS](riscv-ip/kestrel-rv32i/docs/kestrel_has/kestrel_has_index.md) · [MAS](riscv-ip/kestrel-rv32i/docs/kestrel_mas/kestrel_mas_index.md) |
| **merlin / peregrine / gyrfalcon / garuda** | Planned — falcon-suite ladder (structure only; see [suite README](riscv-ip/README.md)) | [riscv-ip/](riscv-ip/) | [Suite design spec](../../docs/superpowers/specs/2026-10-06-riscv-falcon-suite-design.md) |
| **hive-serv (SERV compute cluster)** | Re-homed 2026-10-10 from compute-eng-ip/hive (retired 2026-09-27; revived as a riscv-ip area — 1 VexRiscv + 16 SERV cores, spec only, no RTL yet) | [riscv-ip/hive-serv/](riscv-ip/hive-serv/) | [Specification](riscv-ip/hive-serv/docs/hive_spec/hive_index.md) |
| **amber (blocking MESI snoopy L1 cache)** | In progress — first of the [cache-ip/](cache-ip/) gemstone family; HAS/MAS v1.0, RTL landing | [cache-ip/amber-mesi-l1/](cache-ip/amber-mesi-l1/) | [README](cache-ip/amber-mesi-l1/README.md) · [PRD](cache-ip/amber-mesi-l1/PRD.md) |
| **jet (lockup-free MESI snoopy L1)** | Planned — non-blocking (MSHR) follow-on to amber; [README](cache-ip/jet-mesi-l1/README.md) + [PRD](cache-ip/jet-mesi-l1/PRD.md) scaffolded | [cache-ip/jet-mesi-l1/](cache-ip/jet-mesi-l1/) | — |
| **basalt (MOESI L2)** | Planned — pencil only, PRD v0.1 all rows OPEN; gated behind onyx v1 | [cache-ip/basalt-moesi-l2/](cache-ip/basalt-moesi-l2/) | [README](cache-ip/basalt-moesi-l2/README.md) |
| **onyx (ACE coherence manager / CCU)** | Planned — README + PRD only; owns the ACE-shaped AC/CD/CR snoop port (D7 decided 2026-10-05) | [cache-ip/onyx-ace-ccu/](cache-ip/onyx-ace-ccu/) | [README](cache-ip/onyx-ace-ccu/README.md) |
| **dfx-ip (house debug port)** | Scaffold 2026-10-11 — jtag-tap / jtag-axil-agent / riscv-debug dirs; no RTL | [dfx-ip/](dfx-ip/) | [HAS index](dfx-ip/docs/dfx_has/dfx_has_index.md) |

---

## Quick Links

### By Category

**Timing and Control:**
- [Retro Legacy Blocks](retro_legacy_blocks/) - HPET, 8254 PIT, and other legacy timers/peripherals (absorbed the old apb4_hpet)

**DMA and Data Transfer:**
- [STREAM](dma-ip/stream/) - Tutorial DMA engine
- [RAPIDS](dma-ip/rapids/) - Advanced DMA with network (Done 2026-10-11)

**Interconnect:**
- [APB Crossbar](fabric-gen-ip/apbx-xbar/) - MxN APB interconnect
- [Bridge](fabric-gen-ip/bridge/) - generated AMBA 3/4/5 + Wishbone-4 protocol bridges
- [Delta](fabric-gen-ip/delta/) - AXI-Stream crossbar generator (fabric family); its aspirational NoC draft lives at [noc-ip/delta_spec/](noc-ip/delta_spec/)

**Memory Controllers:**
- [pumice](mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2/) - DDR2/LPDDR2, board-validated on Nexys A7
- [scoria](mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3/) - DDR3/LPDDR3, simulation-verified; board campaign ongoing
- [andesite](mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4/) - DDR4/LPDDR4 directory baseline (planned)
- [product tops](mem-ctrl-ip/product-ip/) - granite / gabbro / diorite scaffolds wrapping the research rocks

**Error correction:**
- [ecc-ip](ecc-ip/) - error-correction IP family: [Reed-Solomon](ecc-ip/reed-solomon/) and [BCH](ecc-ip/bch/), both 1.0 and board-validated

**RISC-V:**
- [kestrel](riscv-ip/kestrel-rv32i/) - RV32I single-cycle core (rv32ui + riscv-formal 42/42)
- [falcon suite](riscv-ip/) - merlin / peregrine / gyrfalcon / garuda ladder (planned)
- [hive-serv](riscv-ip/hive-serv/) - SERV compute cluster, re-homed from compute-eng-ip 2026-10-10 (retired 2026-09-27, revived)

**Cache coherence:**
- [amber](cache-ip/amber-mesi-l1/) - blocking MESI snoopy L1, RTL landing
- [jet / basalt / onyx](cache-ip/) - MSHR L1 · MOESI L2 · ACE CCU (planned)

**Debug and test:**
- [dfx-ip](dfx-ip/) - house debug port: JTAG transport (jtag-tap), config poke agent (jtag-axil-agent), riscv override plane (riscv-debug); scaffolded 2026-10-11

---

## Documentation Structure

Each component follows this standard structure:

```
{component}/
├── rtl/                    # RTL source code
│   ├── {name}_fub/         # Functional unit blocks
│   ├── {name}_macro/       # Top-level integration
│   └── includes/           # Package definitions
├── dv/                     # Design verification
│   ├── tests/              # Test runners
│   ├── tbclasses/          # Testbench classes
│   └── components/         # BFMs (if needed)
├── docs/                   # Component documentation
│   ├── {name}_spec/        # Detailed specification
│   └── IMPLEMENTATION_STATUS.md
├── bin/                    # Component-specific scripts
├── known_issues/           # Issue tracking
├── PRD.md                  # Product requirements
├── CLAUDE.md               # AI assistance guide
├── TASKS.md                # Work tracking
└── README.md               # Quick start
```

---

## Status Legend

- **Production Ready** - Complete, verified, ready for integration
- **Functional** - Working, test cleanup/refinement ongoing
- **In Development** - Active development, partial functionality
- **Planned** - Design phase, not yet implemented

---

## Project-Level Resources

### Documentation
- **[Project README](README.md)** - Overview and getting started
- **[Project PRD](PRD.md)** - Requirements and goals
- **[Project CLAUDE Guide](CLAUDE.md)** - area facts for agents
- **Status** - the live tracker is [vault/Tasks/INDEX.md](../../vault/Tasks/INDEX.md);
  the table above is the only status summary kept here (one source per fact)
- **Running tests** - [vault/handbook/dv/running-regressions.md](../../vault/handbook/dv/running-regressions.md);
  every `dv/tests/Makefile` is four lines that include [make/tests.mk](../../make/tests.mk),
  and this directory's [Makefile](Makefile) drives them all (`make help`)
- **Coverage** - [vault/handbook/dv/coverage.md](../../vault/handbook/dv/coverage.md)

### Testing
- **[Makefile](Makefile)** - Central build and test control
- Run all component tests: `make test`
- Individual component: `make test-{component}`

---

## For More Information

- **Detailed Component Documentation:** [docs/markdown/projects/index.md](../../docs/markdown/projects/index.md)
- **RTL Building Blocks:** [rtl/common/](../../rtl/common/) and [rtl/amba/](../../rtl/amba/)
- **Main Repository Guide:** [Root README](../../README.md)

---

**Maintained By:** RTL Design Sherpa Project
**Last Review:** 2026-09-28 (tooling TASK-004: retired the shared guides that duplicated the handbook)
