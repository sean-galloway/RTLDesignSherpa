<table>
<tr>
<td width="220">
  <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa Logo" width="200">
</td>
<td>
  <h1>RTL Design Sherpa</h1>
  <p><em>Learning Hardware Design Through Practice</em></p>
  <p>
    <img src="https://img.shields.io/badge/SystemVerilog-RTL_Design-0066cc?style=flat-square&logo=v&logoColor=white" alt="SystemVerilog">
    <img src="https://img.shields.io/badge/CocoTB-Verification-00aa55?style=flat-square&logo=python&logoColor=white" alt="CocoTB">
    <img src="https://img.shields.io/badge/Verilator-Simulation-ff6600?style=flat-square" alt="Verilator">
  </p>
  <p>
    <img src="https://img.shields.io/badge/RTL_Modules-350+-blue?style=flat-square" alt="RTL Modules">
    <img src="https://img.shields.io/badge/Components-10+-orange?style=flat-square" alt="Components">
    <img src="https://img.shields.io/badge/License-MIT-green?style=flat-square" alt="License">
    <img src="https://img.shields.io/badge/Open_Source-Tools-purple?style=flat-square" alt="Open Source">
  </p>
</td>
</tr>
</table>

*A progressive learning framework for RTL development using open-source tools*

**📚 [Documentation Index](docs/DOCUMENTATION_INDEX.md)** - Complete guide to all documentation, organized by type

---

## Project Mission

**RTL Design Sherpa guides you through digital hardware design with 
hands-on learning from first principles.**

We start with fundamental building blocks (adders, multipliers, FIFOs), 
progress to protocol-specific modules (AXI, DMA engines), and culminate 
in complete FPGA-ready systems. Every module is both educational and 
production-quality - meeting real timing and resource constraints.

**What makes RTL Design Sherpa different:**

- **From scratch**: Python generators → SystemVerilog → synthesis. 
  No black boxes, every design decision explained.

- **Safety net for exploration**: Comprehensive test suites at every 
  level (unit, integration, formal) let you experiment with confidence. 
  Try different optimizations - the tests catch regressions.

- **Performance-driven**: Multiple implementations of key modules, 
  with measured area/speed tradeoffs. SimPy models predict behavior 
  before writing RTL.

- **Industry practices**: Open-source tools (cocotb, Verilator, Yosys) 
  demonstrating verification methodologies used in production.

- **Complete transparency**: Build systems, Makefiles, debugging 
  sessions - all the "hidden knowledge" made visible.

Whether you're learning your first Verilog module or optimizing a 
high-speed interconnect, RTL Design Sherpa provides the detailed 
explanations, working examples, and verification infrastructure to 
build understanding from the ground up.

### Learning Path

Guided progression from primitives to systems. Each level links to the corresponding section in [Browse by Class](#browse-by-class) below — every entry is a real link (works on mobile and desktop alike).

- **Level 1 — [Common Building Blocks](rtl/common/)** · ~224 modules · counters, FIFOs, arbiters, integer + floating-point math, data integrity, clock utilities
- **Level 2 — [AMBA Protocol Infrastructure](rtl/amba/)** · 155 modules · [AXI4](rtl/amba/axi4/) · [AXI5](rtl/amba/axi5/) · [AXI4-Lite](rtl/amba/axil4/) · [APB](rtl/amba/apb/) · [APB5](rtl/amba/apb5/) · [AXIS4](rtl/amba/axis4/) · [AXIS5](rtl/amba/axis5/) · [Shared (monitor/observation/monbus)](rtl/amba/shared/)
- **Level 3 — [Integration Examples](rtl/integ_amba/)** · APB crossbar, bridges, multi-protocol stitching
- **Level 4 — [Production Components](projects/components/)** · [STREAM](projects/components/stream/) · [RAPIDS](projects/components/rapids/) · [Bridge](projects/components/bridge/) · [Converters](projects/components/converters/) · [APB xbar](projects/components/apb_xbar/) · [Retro legacy](projects/components/retro_legacy_blocks/) · [Memory controllers](projects/components/memory-controllers/)
- **Level 5 — [FPGA Projects on Nexys A7](projects/NexysA7/)** · [stream_characterization](projects/NexysA7/stream_characterization/) · [timing_characterization](projects/NexysA7/timing_characterization/) · [cdc_counter_display](projects/NexysA7/cdc_counter_display/) · [ddr2-lpddr2-memory-controller](projects/NexysA7/ddr2-lpddr2-memory-controller/)

<details>
<summary>Visual diagram (Mermaid — desktop browsers only)</summary>

```mermaid
graph TD
    L1[Level 1: Common Building Blocks<br/>~224 modules] --> L2[Level 2: AMBA Protocol Infrastructure<br/>155 modules]
    L2 --> L3[Level 3: Integration Examples]
    L3 --> L4[Level 4: Production Components<br/>10+ components]
    L4 --> L5[Level 5: Complete FPGA Projects]

    L1 -.- L1D[Counters, FIFOs, Arbiters<br/>Math, Floating-Point, Data Integrity]
    L2 -.- L2D[AXI4, AXI5, AXI4-Lite, APB, APB5<br/>AXIS4, AXIS5, Shared monitor/observation]
    L3 -.- L3D[APB Crossbar, Bridges, multi-protocol stitching]
    L4 -.- L4D[STREAM, RAPIDS, Bridge, Converters<br/>Retro Legacy Blocks, Memory controllers]
    L5 -.- L5D[stream_characterization, timing_characterization<br/>cdc_counter_display, ddr2-lpddr2-memory-controller]

    click L1 "rtl/common/" "Common Building Blocks"
    click L2 "rtl/amba/" "AMBA Protocol Infrastructure"
    click L3 "rtl/integ_amba/" "Integration Examples"
    click L4 "projects/components/" "Production Components"
    click L5 "projects/NexysA7/" "FPGA Projects"
```

</details>

---

## Browse by Class

Fast lookup. Each row is a class of things; the deep-dive link goes to its index/spec. For a guided tour through the levels, see [Progressive Learning Approach](#progressive-learning-approach) further down.

> Counts are approximate as of 2026-06-24; subsystem READMEs are authoritative.

### 1. Common Building Blocks — `rtl/common/`

Reusable primitives, technology-agnostic. **~224 modules.**

| Class | ~Count | Where | Examples |
|---|---|---|---|
| Counters | 8 | `rtl/common/counter_*.sv` | `counter_bin`, `counter_bingray`, `counter_load_clear`, `counter_johnson`, `counter_ring`, `counter_freq_invariant` |
| Arbiters | 4 | `rtl/common/arbiter_*.sv` | `arbiter_round_robin`, `arbiter_round_robin_weighted`, PWM variants |
| FIFOs | 4 | `rtl/common/fifo_*.sv` | `fifo_sync`, `fifo_async`, `fifo_async_div2`, `fifo_sync_multi` |
| Shift / LFSR | — | `rtl/common/shifter_lfsr_*.sv` | Fibonacci LFSR, Galois LFSR, universal shifters |
| Math — integer arithmetic | 40+ | `rtl/common/math_adder_*`, `math_mult_*`, `math_div_*` | Han-Carlson prefix adders (16/22/32/44/48/72-bit), Dadda 4:2 compressor mults (8/11/24-bit), leading-zero count, parity |
| Math — floating point | 120+ | `rtl/common/math_float_*` | BF16, FP16, FP32, FP8 (E4M3/E5M2): adder, multiplier, FMA, recip, divide, sqrt; cross-format converters |
| Data integrity | 7 | `rtl/common/dataint_*.sv` | `dataint_crc` (300+ standards), `dataint_ecc_hamming` (SECDED), `dataint_parity` |
| Clock utilities | 3 | `rtl/common/clock_*.sv` | `clock_divider`, `clock_gate_ctrl`, `clock_pulse` |
| Encoders / decoders | 3 | `rtl/common/{encoder,decoder}*.sv` | priority encoder, address decoder |
| Reset | 1 | `rtl/common/reset_sync.sv` | async-assert / sync-deassert reset bridge |

**Deep dive:** [`docs/markdown/RTLCommon/index.md`](docs/markdown/RTLCommon/index.md) · [`rtl/common/CLAUDE.md`](rtl/common/CLAUDE.md)

### 2. AMBA Protocols — `rtl/amba/`

Production-ready AXI/APB/AXIS infrastructure with built-in monitor + observation. **155 modules across 8 protocol dirs + 48 shared.**

| Protocol | Modules | Where | Notes |
|---|---|---|---|
| AXI4 | 16 | `rtl/amba/axi4/` | masters/slaves, RD/WR, `_mon` + `_cg` variants |
| AXI5 | 16 | `rtl/amba/axi5/` | AXI5 extensions |
| AXI4-Lite | 16 | `rtl/amba/axil4/` | **Dedicated** `axil4_*_mon.sv` (not the legacy `IS_AXI=0`) |
| APB | 9 | `rtl/amba/apb/` | masters, slaves, slave_cdc + `_cg` |
| APB5 | 9 | `rtl/amba/apb5/` | APB5 extensions |
| AXI-Stream (AXIS4) | 4 | `rtl/amba/axis4/` | master / slave |
| AXI-Stream (AXIS5) | 4 | `rtl/amba/axis5/` | AXIS5 extensions |
| Shared infrastructure | 48 | `rtl/amba/shared/` | monitor core, monbus, observation, sdpram, CDC, arbiters |
| GAXI generic | 8 | `rtl/amba/gaxi/` | sync/async FIFOs and skid buffers |
| Packages | 8 | `rtl/amba/includes/` | shared `.svh`/types |

**Deep dive:** [`rtl/amba/README.md`](rtl/amba/README.md) (full shared/ inventory by role) · [`rtl/amba/CLAUDE.md`](rtl/amba/CLAUDE.md) · [`docs/markdown/RTLAmba/index.md`](docs/markdown/RTLAmba/index.md)

### 3. Clock Domain Crossing (CDC) — Cross-cutting

CDC primitives live in multiple subsystems. Pulled together here so you don't have to hunt.

| Module | Where | Use |
|---|---|---|
| `cdc_synchronizer.sv` | `rtl/amba/shared/` | Plain N-flop bit synchronizer |
| `cdc_2_phase_handshake.sv` | `rtl/amba/shared/` | 2-phase req/ack data CDC |
| `cdc_4_phase_handshake.sv` | `rtl/amba/shared/` | 4-phase req/ack data CDC |
| `cdc_open_loop.sv` | `rtl/amba/shared/` | Fire-and-forget pulse CDC |
| `reset_sync.sv` | `rtl/common/` | Async-assert / sync-deassert reset CDC |
| `bin2gray.sv` / `gray2bin.sv` | `rtl/common/` | Gray-code conversion for pointer CDC |
| `counter_bingray.sv` | `rtl/common/` | Binary/Gray dual counter for FIFO pointers |
| `fifo_async.sv` / `fifo_async_div2.sv` | `rtl/common/` | Async FIFOs for word-width CDC |
| `gaxi_fifo_async*.sv`, `gaxi_skid_buffer_async*.sv` | `rtl/amba/gaxi/` | AXI-shaped async FIFO + skid |
| `apb_slave_cdc.sv` / `apb5_slave_cdc.sv` | `rtl/amba/apb*/` | APB slave with CDC built in |

**FPGA demo:** [`projects/NexysA7/cdc_counter_display/`](projects/NexysA7/cdc_counter_display/) — multi-clock counter CDC running on real hardware.

### 4. Component Projects — `projects/components/`

Production-shaped reusable IP. Each has its own README + dv/ + dv/tbclasses/.

| Project | Status | Domain | Where |
|---|---|---|---|
| STREAM | ✅ Ready | Tutorial DMA + scatter-gather | [`projects/components/stream/`](projects/components/stream/) |
| RAPIDS | 🟡 In progress | Advanced DMA with network interfaces (RAPID AXI Programmable In-band Descriptor System) | [`projects/components/rapids/`](projects/components/rapids/) |
| Bridge | ✅ Ready | AXI protocol bridges + RDL-generated cfg | [`projects/components/bridge/`](projects/components/bridge/) |
| Converters | ✅ Ready | UART↔AXIL, protocol conversion | [`projects/components/converters/`](projects/components/converters/) |
| APB Crossbar | ✅ Ready | M×N APB interconnect | [`projects/components/apb_xbar/`](projects/components/apb_xbar/) |
| BCH | — | BCH error-correction codec | [`projects/components/bch/`](projects/components/bch/) |
| Memory controllers | 🟡 In progress | DDR2 / LPDDR2 controller | [`projects/components/memory-controllers/`](projects/components/memory-controllers/) |
| Retro legacy blocks | ✅ Ready | HPET, PIC, PIT, RTC, UART, GPIO | [`projects/components/retro_legacy_blocks/`](projects/components/retro_legacy_blocks/) |
| Delta | 📋 Planned | Network-on-Chip mesh | [`projects/components/delta/`](projects/components/delta/) |
| HIVE | 📋 Planned | Distributed RISC-V control | [`projects/components/hive/`](projects/components/hive/) |
| Misc | — | Mixed building blocks | [`projects/components/misc/`](projects/components/misc/) |

### 5. FPGA Projects — `projects/NexysA7/` (Digilent Nexys A7-100T)

Things that actually run on hardware. Each project ships its own README and Vivado flow.

| Project | Goal | Where |
|---|---|---|
| stream_characterization | DMA performance characterization on FPGA + host-side analysis (UART control, on-chip PMU) | [`projects/NexysA7/stream_characterization/`](projects/NexysA7/stream_characterization/) |
| timing_characterization | FUB delay characterization. STA-only `bitstream-sweep` is the headline path; on-board MMCM sweep is an optional gut-check (see [`README_FPGA.md`](projects/NexysA7/timing_characterization/README_FPGA.md) §5) | [`projects/NexysA7/timing_characterization/`](projects/NexysA7/timing_characterization/) |
| cdc_counter_display | Live demo of multi-clock counter CDC on the board | [`projects/NexysA7/cdc_counter_display/`](projects/NexysA7/cdc_counter_display/) |
| ddr2-lpddr2-memory-controller | DDR2 / LPDDR2 memory controller bring-up on Nexys A7 | [`projects/NexysA7/ddr2-lpddr2-memory-controller/`](projects/NexysA7/ddr2-lpddr2-memory-controller/) |
| boards | Board files / pinouts / constraints | [`projects/NexysA7/boards/`](projects/NexysA7/boards/) |

### 6. Verification

| What | Where |
|---|---|
| AMBA protocol tests | [`val/amba/`](val/amba/) |
| Common-library tests | [`val/common/`](val/common/) |
| Project tests (CocoTB + pytest, Pattern B) | `projects/components/*/dv/tests/` |
| Project-specific TBs | `projects/components/*/dv/tbclasses/` |
| Shared TB framework | [`bin/TBClasses/`](bin/TBClasses/) |
| BFMs / scoreboards (external package) | [`cocotb-framework` on PyPI](https://pypi.org/project/cocotb-framework/) — source: [RTLDesignSherpa-DV](https://github.com/sean-galloway/RTLDesignSherpa-DV) — `pip install cocotb-framework` |
| Verification architecture rules | [`rtl/amba/VERIFICATION_ARCHITECTURE.md`](rtl/amba/VERIFICATION_ARCHITECTURE.md), [`GLOBAL_REQUIREMENTS.md`](GLOBAL_REQUIREMENTS.md) |

### 7. Tools

| Tool | Purpose | Where |
|---|---|---|
| RTL generators | Codegen for math circuits + floating-point modules | [`bin/rtl_generators/`](bin/rtl_generators/) |
| `md_to_docx.py` | Markdown → DOCX/PDF with corporate styles | [`bin/md_to_docx.py`](bin/md_to_docx.py) |
| `audit_signal_naming_conflicts.py` | Detect AXI-factory pattern collisions before TB write | [`bin/audit_signal_naming_conflicts.py`](bin/audit_signal_naming_conflicts.py) ([guide](bin/SIGNAL_NAMING_AUDIT.md)) |
| `vivado_timing_failures.py` | Per-violation Vivado timing parser | [`bin/vivado_timing_failures.py`](bin/vivado_timing_failures.py) |
| Misc scripts | Build/regen helpers, codemaps, doc generators | [`bin/`](bin/), [`tools/`](tools/), [`scripts/`](scripts/) |

### 8. Documentation hub

- [`docs/DOCUMENTATION_INDEX.md`](docs/DOCUMENTATION_INDEX.md) — full doc index
- [`docs/markdown/RTLCommon/index.md`](docs/markdown/RTLCommon/index.md) — per-module specs (common library)
- [`docs/markdown/RTLAmba/index.md`](docs/markdown/RTLAmba/index.md) — per-module specs (AMBA)
- [`docs/markdown/projects/index.md`](docs/markdown/projects/index.md) — project documentation index
- [`GLOBAL_REQUIREMENTS.md`](GLOBAL_REQUIREMENTS.md) — mandatory requirements across the whole repo
- [`CLAUDE.md`](CLAUDE.md) — guidance for AI assistants working in this repo

---

## Progressive Learning Approach

### Level 1: Common Building Blocks (Foundation)

**Location:** [`rtl/common/`](rtl/common/) | **Documentation:** [Full Index](docs/markdown/RTLCommon/index.md) | [AI Guide](rtl/common/CLAUDE.md)

Learn fundamental RTL design patterns through **224 reusable modules**:

#### Integer Arithmetic (44+ modules)
- **Counters:** Binary, Gray code, Johnson, Ring, Load/Clear variants
- **Adders:** Han-Carlson prefix adders (16/22/32/44/48/72-bit), Brent-Kung
- **Multipliers:** Dadda 4:2 compressor trees (8/11/24-bit)
- **Math:** Leading zeros, bit reversal, parity, CRC

#### Floating-Point (120+ modules)
- **BF16:** Adder, multiplier, FMA, reciprocal, division, square root
- **FP16 (IEEE 754):** Complete arithmetic suite
- **FP32 (IEEE 754):** Adder, multiplier, FMA
- **FP8 (E4M3/E5M2):** ML-optimized formats
- **Converters:** Cross-format conversion (FP32↔FP16↔BF16↔FP8)

#### Data Structures
- **FIFOs:** Synchronous, asynchronous, dual-clock domain
- **Shift Registers:** LFSR (Fibonacci/Galois), universal shifters
- **Memory:** CAM (Content Addressable Memory), buffers

#### Control Logic
- **Arbiters:** Round-robin (simple, weighted, PWM), priority encoders
- **Encoders/Decoders:** Priority encoding, address decoding
- **Clock Management:** Dividers, gate control, pulse generation
- **Reset:** Synchronizers, CDC utilities

#### Data Integrity
- **CRC Engines:** Generic CRC supporting 300+ standards
- **ECC:** Hamming code (SECDED), parity checkers

**Example Module:** `counter_bin.sv`
```systemverilog
// Simple binary counter - foundation for timers, state machines
module counter_bin #(
    parameter WIDTH = 8
) (
    input  logic             i_clk,
    input  logic             i_rst_n,
    input  logic             i_enable,
    output logic [WIDTH-1:0] o_count
);
```

**Tests:** [`val/common/`](val/common/) - Every module has comprehensive CocoTB tests

---

### Level 2: AMBA Protocol Infrastructure

**Location:** [`rtl/amba/`](rtl/amba/) | **Documentation:** [Full Index](docs/markdown/RTLAmba/index.md) | [AI Guide](rtl/amba/CLAUDE.md)

Apply common building blocks to implement industry-standard protocols (**124 modules**):

#### APB (Advanced Peripheral Bus)
- **[APB Masters](rtl/amba/apb/)** - Command/response interfaces with FIFO buffering
- **[APB Slaves](rtl/amba/apb/)** - Register interfaces with address decoding
- **[APB Interconnect](rtl/integ_amba/)** - Multi-master/multi-slave crossbar
- **[APB Bridges](rtl/amba/apb/)** - Protocol conversion, CDC

**Example:** APB register slave demonstrates parameter-driven design
```systemverilog
apb_slave #(
    .ADDR_WIDTH(12),
    .DATA_WIDTH(32)
) u_apb_slave (
    .pclk, .presetn, .paddr, .psel, .penable, .pwrite,
    .pwdata, .pready, .prdata, .pslverr
);
```

#### AXI4 Full Protocol
- **[AXI4 Masters](rtl/amba/axi4/)** - Read/write with dual skid buffers
- **[AXI4 Slaves](rtl/amba/axi4/)** - Response generation, address decoding
- **[AXI4 Infrastructure](rtl/amba/gaxi/)** - FIFOs, skid buffers, arbiters
- **[Monitoring](rtl/amba/axi4/)** - Protocol compliance checkers

#### AXI4-Lite (Simplified Register Interface)
- **[AXI4-Lite Masters](rtl/amba/axil4/)** - Register-optimized masters
- **[AXI4-Lite Slaves](rtl/amba/axil4/)** - Configuration registers
- **[Protocol Bridges](rtl/amba/adapters/)** - APB ↔ AXI-Lite conversion

#### AXI4-Stream (High-Throughput Data)
- **[Stream Masters/Slaves](rtl/amba/axis/)** - Streaming interfaces
- **[Flow Control](rtl/amba/axis/)** - Backpressure, buffering
- **[Sideband Support](rtl/amba/axis/)** - TID, TDEST, TUSER, TSTRB

#### Shared Infrastructure
- **[GAXI Buffers](rtl/amba/gaxi/)** - Generic skid buffers, FIFOs, CDC
- **[Monitors](rtl/amba/shared/)** - Transaction monitoring, performance analysis
- **[Arbiters](rtl/amba/shared/)** - Advanced arbitration for monitor buses

**Tests:** [`val/amba/`](val/amba/) - Protocol compliance and integration tests

---

### Level 3: Integration Examples

**Locations:** [`rtl/integ_common/`](rtl/integ_common/) | [`rtl/integ_amba/`](rtl/integ_amba/)

Practice integrating multiple modules into working systems:

#### Simple Integrations (`integ_common`)
- **CDC Counter Display** - Cross clock domain counter with display logic
- **Multi-Clock Systems** - Demonstrate CDC techniques

**Example:** CDC Counter Display
```
Clock Domain A (Fast)    Clock Domain B (Slow)
    Counter      →  CDC  →    Display
   @ 100MHz         Sync      @ 10MHz
```

#### Protocol Integrations (`integ_amba`)
- **APB Crossbar** - Multi-master to multi-slave interconnect
  - 1-to-1, 1-to-4, 2-to-1, 2-to-4 configurations
  - Address decoding, weighted arbitration
- **APB Bridges** - Protocol conversion examples
- **AXI Systems** - Multi-component integration

**Tests:** [`val/integ_common/`](val/integ_common/) | [`val/integ_amba/`](val/integ_amba/)

---

### Level 4: Production Components

**Location:** [`projects/components/`](projects/components/) | **Documentation:** [Component Index](docs/markdown/projects/index.md)

Build complete, production-ready peripherals for FPGA deployment (**10+ components**):

#### DMA Engines

| Component | Status | Description |
|-----------|--------|-------------|
| **[STREAM](projects/components/stream/)** | ✅ Ready | Tutorial DMA with 8 channels, scatter-gather, APB config |
| **[RAPIDS](projects/components/rapids/)** | 🟡 In Progress | Advanced DMA with alignment fixup, network TX/RX, credit flow |

#### Interconnect and Bridges

| Component | Status | Description |
|-----------|--------|-------------|
| **[APB Crossbar](projects/components/apb_xbar/)** | ✅ Ready | Parametric M×N APB interconnect with round-robin arbitration |
| **[Bridge](projects/components/bridge/)** | ✅ Ready | AXI4 protocol bridges, width converters, CDC |
| **[Converters](projects/components/converters/)** | ✅ Ready | UART-to-AXI4-Lite, protocol conversion bridges |

#### Retro Legacy Blocks

**Status:** ✅ Production Ready | **Location:** [`projects/components/retro_legacy_blocks/`](projects/components/retro_legacy_blocks/)

Collection of 9 legacy/retro peripherals with full APB interfaces:

| Peripheral | Description |
|------------|-------------|
| **HPET** | High Precision Event Timer (2/3/8 timers, 64-bit) |
| **GPIO** | General Purpose I/O with interrupts |
| **UART 16550** | Full 16550-compatible UART |
| **8259 PIC** | Programmable Interrupt Controller |
| **8254 PIT** | Programmable Interval Timer |
| **RTC** | Real-Time Clock |
| **SMBUS** | System Management Bus controller |
| **PM/ACPI** | Power Management / ACPI support |
| **IOAPIC** | I/O Advanced PIC |

**Documentation:** [Block Status](projects/components/retro_legacy_blocks/BLOCK_STATUS.md) | [PRD](projects/components/retro_legacy_blocks/PRD.md)

#### Future Components

| Component | Status | Description |
|-----------|--------|-------------|
| **[Delta](projects/components/delta/)** | 📋 Planned | 4×4 Network-on-Chip mesh with virtual channels |
| **[HIVE](projects/components/hive/)** | 📋 Planned | Distributed RISC-V control (VexRiscv + 16 SERV monitors) |
| **[BCH](projects/components/bch/)** | 📋 Planned | BCH error correction encoder/decoder |

---

### Level 5: Complete FPGA Projects (Future)

**Planned:** Full SoC designs combining all levels:

- **Simple SoC:** APB HPET + Memory + UART
- **DMA System:** RAPIDS DMA + Multi-bank memory
- **Communication Hub:** Ethernet MAC + DMA + Buffers
- **Processing Subsystem:** Custom accelerators + Interconnect

---

## Verification Methodology

### CocoTB-Based Testing

Every module demonstrates professional verification practices:

**Test Structure:**
```python
# Reusable testbench class (in bin/TBClasses/)
class ModuleTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.setup_drivers()
        self.setup_monitors()
        self.setup_scoreboards()

    async def setup_clocks_and_reset(self):
        """Standard clock and reset initialization"""

    async def write_register(self, addr, data):
        """Protocol-specific register write"""

# Test suite (organized by level)
class ModuleBasicTests:
    async def test_register_access(self): ...
    async def run_all_basic_tests(self): ...

class ModuleMediumTests:
    async def test_complex_scenario(self): ...
    async def run_all_medium_tests(self): ...

class ModuleFullTests:
    async def test_stress(self): ...
    async def run_all_full_tests(self): ...
```

**Test Hierarchy:**
1. **Basic Tests** - Register access, reset behavior, simple operations
2. **Medium Tests** - Complex features, multi-component interactions
3. **Full Tests** - Stress testing, CDC, edge cases

**Test Configuration (conftest.py):**
- Auto-creates logs directory
- Registers pytest markers (basic, medium, full)
- Preserves all logs
- Parametrized test fixtures

**Running Tests:**
```bash
# Run all tests for a module
pytest val/common/test_counter_bin.py -v

# Run specific test level
pytest val/amba/ -v -m basic      # Basic tests only
pytest val/amba/ -v -m medium     # Medium tests only
pytest val/amba/ -v -m full       # Full tests only

# Run component tests (example: Retro Legacy Blocks)
pytest projects/components/retro_legacy_blocks/dv/tests/hpet/ -v
```

---

## Technology Stack

### Core Tools (All Open-Source)

#### Simulation and Analysis
- **[Verilator](https://verilator.org/)** - High-performance RTL simulator
  - Supports SystemVerilog
  - VCD/FST waveform generation
  - Fast execution for large designs
- **[GTKWave](http://gtkwave.sourceforge.net/)** - Waveform viewer
  - Pre-configured signal groups
  - Professional visualization
- **[Verible](https://github.com/chipsalliance/verible)** - SystemVerilog tools
  - Linting and style checking
  - Code formatting
  - Parsing and analysis

#### Verification Framework
- **[CocoTB](https://docs.cocotb.org/)** - Python-based testbench framework
  - Intuitive Python test writing
  - Full SystemVerilog integration
  - Extensive protocol libraries
- **[pytest](https://pytest.org/)** - Test runner and framework
  - Test discovery and execution
  - Parametrized testing
  - Rich reporting
- **Custom VIP** - Verification IP for protocols
  - APB, AXI4, AXI4-Lite, AXI-Stream drivers/monitors
  - Scoreboards and coverage collectors

#### Register Generation
- **[PeakRDL](https://peakrdl.readthedocs.io/)** - SystemRDL tools
  - Register file generation from specifications
  - APB4, AXI4-Lite interface generation
  - C header generation
  - Documentation generation

#### Development and Automation
- **Python 3.8+** - Scripting and automation
  - Code generation (math circuits, register files)
  - Analysis tools (dependency, UML)
  - Documentation generation (Wavedrom)
- **Make** - Build automation
- **Git** - Version control with CI/CD integration

---

## Repository Structure

```
rtldesignsherpa/
├── rtl/                          # RTL source code (350+ modules)
│   ├── common/                   # 224 building blocks (counters, math, FP, etc.)
│   ├── amba/                     # 124 AMBA protocol modules
│   │   ├── apb/                 # APB protocol
│   │   ├── axi4/                # AXI4 full protocol
│   │   ├── axil4/               # AXI4-Lite
│   │   ├── axis/                # AXI4-Stream
│   │   ├── axi5/                # AMBA5 components
│   │   ├── apb5/                # APB5 protocol
│   │   ├── gaxi/                # Generic AXI infrastructure
│   │   └── shared/              # Shared utilities (CDC, monitors)
│   ├── integ_common/            # Common integration examples
│   └── integ_amba/              # AMBA integration examples
│
├── projects/                     # Component projects (10+)
│   ├── components/
│   │   ├── stream/              # STREAM DMA engine
│   │   ├── rapids/              # RAPIDS DMA engine
│   │   ├── bridge/              # Protocol bridges
│   │   ├── converters/          # UART-to-AXI4-Lite, etc.
│   │   ├── apb_xbar/            # APB crossbar
│   │   ├── retro_legacy_blocks/ # 9 legacy peripherals
│   │   ├── delta/               # Network-on-Chip (planned)
│   │   ├── hive/                # RISC-V control (planned)
│   │   └── bch/                 # BCH ECC (planned)
│   └── NexysA7/                 # FPGA projects
│
├── val/                          # Validation/Test suites
│   ├── common/                  # Common module tests
│   └── amba/                    # AMBA protocol tests
│
├── bin/                          # Tools and automation
│   ├── CocoTBFramework/         # Testbench infrastructure (200+ files)
│   ├── rtl_generators/          # RTL code generators
│   │   ├── bf16/                # BF16 floating-point generators
│   │   ├── ieee754/             # IEEE 754 FP generators
│   │   └── verilog/             # Generic RTL generators
│   ├── md_to_docx.py            # Documentation generator
│   └── update_doc_headers.py    # Header management
│
├── docs/                         # Documentation
│   ├── markdown/                # Technical documentation
│   │   ├── RTLCommon/           # Common library docs
│   │   ├── RTLAmba/             # AMBA library docs
│   │   ├── CocoTBFramework/     # Framework docs
│   │   └── projects/            # Component docs
│   └── DOCUMENTATION_INDEX.md   # Master doc index
│
├── CLAUDE.md                     # Repository AI guide
└── README.md → docs/markdown/overview.md  # This file (symlink)
```

---

## Getting Started

### Installation

**1. Install Prerequisites:**
```bash
# Ubuntu/Debian
sudo apt update
sudo apt install -y verilator gtkwave python3 python3-pip git make

# Fedora/RHEL
sudo dnf install -y verilator gtkwave python3 python3-pip git make

# macOS (via Homebrew)
brew install verilator gtkwave python3 git make
```

**2. Install Python Dependencies:**
```bash
pip3 install cocotb pytest cocotb-test
pip3 install peakrdl peakrdl-regblock  # For register generation
```

**3. Clone Repository:**
```bash
git clone https://github.com/yourusername/rtldesignsherpa.git
cd rtldesignsherpa
```

### Quick Start Examples

#### Level 1: Test a Simple Counter
```bash
# Run basic counter test
pytest val/common/test_counter_bin.py -v

# View waveforms (after test generates VCD)
gtkwave val/common/local_sim_build/test_counter_bin/dump.vcd
```

#### Level 2: Test APB Slave
```bash
# Run APB slave tests
pytest val/amba/test_apb_slave.py -v

# Run only basic tests
pytest val/amba/test_apb_slave.py -v -m basic
```

#### Level 3: Test APB Crossbar Integration
```bash
# Run 2-to-4 crossbar test
pytest val/integ_amba/test_apb_xbar.py -v -k "2to4"
```

#### Level 4: Test Retro Legacy Block Component
```bash
# Run HPET tests from Retro Legacy Blocks collection
pytest projects/components/retro_legacy_blocks/dv/tests/hpet/ -v

# Run specific test
pytest projects/components/retro_legacy_blocks/dv/tests/hpet/test_apb_hpet.py -v
```

---

## Learning Resources

### Documentation by Level

**Level 1 - Common Modules:**
- [Common Library PRD](rtl/common/PRD.md) - Requirements and specifications
- [Common CLAUDE Guide](rtl/common/CLAUDE.md) - AI-assisted development
- [Common Tests](val/common/) - Example test patterns

**Level 2 - AMBA Protocols:**
- [AMBA Infrastructure PRD](rtl/amba/PRD.md) - Protocol specifications
- [AMBA CLAUDE Guide](rtl/amba/CLAUDE.md) - Implementation patterns
- [AMBA Tests](val/amba/) - Protocol compliance tests

**Level 3 - Integration:**
- [Integration Examples](rtl/integ_amba/) - Working multi-module designs
- [Integration Tests](val/integ_amba/) - System-level verification

**Level 4 - Components:**
- [Component Index](docs/markdown/projects/index.md) - All components
- [Component Overview](docs/markdown/projects/overview.md) - Design patterns
- [Retro Legacy Blocks](projects/components/retro_legacy_blocks/README.md) - Legacy peripheral collection
- [HPET Specification](projects/components/retro_legacy_blocks/docs/hpet_spec/hpet_index.md) - Complete HPET guide

### External References

**Standards:**
- [AMBA Specifications](https://developer.arm.com/architectures/system-architectures/amba) - ARM protocols
- [SystemRDL 2.0](https://www.accellera.org/downloads/standards/systemrdl) - Register specification

**Tools:**
- [CocoTB Documentation](https://docs.cocotb.org/) - Verification framework
- [Verilator Manual](https://verilator.org/guide/latest/) - Simulator guide
- [PeakRDL Docs](https://peakrdl.readthedocs.io/) - Register generation

**Books Referenced:**
- *Advanced FPGA Design* by Steve Kilts
- *Synthesis of Arithmetic Circuits* by Deschamps, Bioul, Sutter

---

## Development Workflow

### Creating a New Module

**1. Design the Module (choose your level):**
```systemverilog
// rtl/common/my_module.sv (Level 1)
// or
// rtl/amba/my_protocol.sv (Level 2)
module my_module #(
    parameter WIDTH = 8
) (
    input  logic             i_clk,
    input  logic             i_rst_n,
    // ... ports
);
```

**2. Create Testbench:**
```python
# bin/TBClasses/{subsystem}/my_module_tb.py
class MyModuleTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)

    async def setup_clocks_and_reset(self):
        # Clock and reset initialization
        pass

# bin/TBClasses/{subsystem}/my_module_tests_basic.py
class MyModuleBasicTests:
    async def test_basic_functionality(self):
        # Test implementation
        pass
```

**3. Create Test Runner:**
```python
# val/{subsystem}/test_my_module.py
import cocotb
import pytest
from cocotb_test.simulator import run

from TBClasses.{subsystem}.my_module_tb import MyModuleTB
from TBClasses.{subsystem}.my_module_tests_basic import MyModuleBasicTests

@cocotb.test()
async def my_module_test(dut):
    tb = MyModuleTB(dut)
    await tb.setup_clocks_and_reset()
    tests = MyModuleBasicTests(tb)
    result = await tests.run_all_basic_tests()
    assert result

@pytest.mark.parametrize("width", [8, 16, 32])
def test_my_module(request, width):
    run(verilog_sources=[...], parameters={'WIDTH': width}, ...)
```

**4. Run Tests:**
```bash
pytest val/{subsystem}/test_my_module.py -v
```

**5. Document:**
- Add to subsystem PRD.md
- Update CLAUDE.md with patterns
- Create examples in documentation

---

## Performance and Quality

### Test Coverage

**Current Status:**
- **Common Library:** >95% line coverage, >90% branch coverage
- **AMBA Protocols:** >95% line coverage, 100% protocol compliance
- **APB HPET:** 5/6 configurations at 100% (12 tests each)
- **Integration:** Full system-level verification

### Module Counts

- **224 Common Modules** - Counters, FIFOs, arbiters, math, floating-point
- **124 AMBA Modules** - APB, AXI4, AXI4-Lite, AXI-Stream, AMBA5
- **10+ Production Components** - DMA engines, bridges, legacy peripherals
- **350+ Total RTL Modules** - Complete verification infrastructure

### Synthesis Results

Modules have been characterized across FPGA technologies:

| Category | Fmax Range | Use Cases |
|----------|------------|-----------|
| Basic Logic | 100-800 MHz | Counters, registers, control |
| Advanced Math | 200-600 MHz | DSP, arithmetic operations |
| Protocol Masters/Slaves | 200-500 MHz | APB, AXI interfaces |
| Integration Examples | 100-400 MHz | Multi-module systems |
| Production Components | 100-200 MHz | Complete peripherals |

---

## Contributing

We welcome contributions at all levels:

**Level 1-2:** New building blocks or protocol modules
**Level 3:** Integration examples and use cases
**Level 4:** Production components
**Level 5:** Complete FPGA projects

**Guidelines:**
- Follow existing module structure and naming
- Include comprehensive CocoTB tests (3-level hierarchy)
- Document in PRD.md and CLAUDE.md
- Achieve >95% test coverage
- Provide integration examples

---

## Use Cases

### Educational
- **University Courses:** Complete RTL design curriculum
- **Self-Learning:** Progressive path from basics to production
- **Industry Preparation:** Professional verification practices

### Professional
- **IP Development:** Starting point for commercial IP
- **Prototyping:** Rapid hardware proof-of-concept
- **Tool Evaluation:** Open-source vs. commercial comparison

### Startup/Small Teams
- **Cost-Effective Development:** No expensive EDA licenses
- **Team Training:** Standardized practices and workflows
- **IP Portfolio:** Foundation for valuable hardware assets

---

## Roadmap

### Current Focus
- ✅ **STREAM DMA** - Tutorial DMA engine complete
- ✅ **Bridge components** - AXI4 width converters, CDC bridges complete
- ✅ **Retro Legacy Blocks** - 9 peripherals with MAS documentation
- 🟡 **RAPIDS DMA** - Advanced DMA in progress
- 🟡 **Floating-Point** - FP32 FMA, additional converters

### Near-Term
- Delta Network-on-Chip mesh implementation
- HIVE distributed RISC-V control
- BCH error correction codec
- NexysA7 FPGA integration examples

### Long-Term
- Complete SoC reference designs
- PCIe/Ethernet/USB controllers
- Formal verification integration
- ASIC synthesis flow examples

---

## Project Philosophy

**RTL Design Sherpa believes that:**

1. **Learning by Doing** - Best way to learn hardware design is building real circuits
2. **Progressive Complexity** - Start simple, build up systematically
3. **Verification First** - Quality comes from comprehensive testing
4. **Open Source** - Knowledge should be accessible to everyone
5. **Industry Practices** - Teach real-world professional techniques

**The journey from a simple counter to a complete DMA engine teaches not just RTL, but the entire hardware development process.**

---

## License

[Your License Here]

---

## Contact and Support

- **GitHub Issues:** [Report issues or request features]
- **Documentation:** [Link to docs]
- **Community:** [Link to discussions/forum]

---

*RTL Design Sherpa: Guiding you from first principles to production-ready hardware design.*
