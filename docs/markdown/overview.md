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

**[Documentation Index](../DOCUMENTATION_INDEX.md)** - Complete guide to all documentation, organized by type

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

```mermaid
graph TD
    L1[Level 1: Common Building Blocks<br/>224 modules] --> L2[Level 2: AMBA Protocol Infrastructure<br/>124 modules]
    L2 --> L3[Level 3: Integration Examples]
    L3 --> L4[Level 4: Production Components<br/>10+ components]
    L4 --> L5[Level 5: Complete FPGA Projects]

    L1 -.- L1D[Counters, FIFOs, Arbiters<br/>Math, Floating-Point, Data Integrity]
    L2 -.- L2D[APB, AXI4, AXI4-Lite<br/>AXI-Stream, ACE, AMBA5 protocols]
    L3 -.- L3D[CDC Counter Display<br/>APB Crossbar, Bridges]
    L4 -.- L4D[STREAM, RAPIDS, Bridge<br/>Converters, Retro Legacy Blocks]
    L5 -.- L5D[NexysA7 FPGA Projects<br/>Full SoC designs]
```

---

## Quick Navigation

### Documentation
- **[Component Projects Index](projects/index.md)** - All production-ready components
- **[Documentation Index](../DOCUMENTATION_INDEX.md)** - Complete documentation guide

### RTL Building Blocks
- **[Common Library](../../rtl/common)** (224 modules) - [Documentation](rtl-common/index.md) - [AI Guide](../../rtl/common/CLAUDE.md)
  - Counters, FIFOs, arbiters, integer math, floating-point (BF16/FP16/FP32/FP8), data integrity
- **[AMBA Infrastructure](../../rtl/amba)** (124 modules) - [Documentation](rtl-amba/index.md) - [AI Guide](../../rtl/amba/CLAUDE.md)
  - APB, AXI4, AXI4-Lite, AXI-Stream, ACE, AMBA5 protocols

### Component Projects
| Component | Status | Description |
|-----------|--------|-------------|
| **[STREAM](../../projects/components/dma-ip/stream)** | Ready | Tutorial DMA engine with scatter-gather |
| **[RAPIDS](../../projects/components/dma-ip/rapids)** | Ready | Advanced DMA with network interfaces (qualified 2026-10-11) |
| **[Bridge](../../projects/components/fabric-gen-ip/bridge)** | Ready | Generated AMBA 3/4/5 + Wishbone-4 protocol bridges, RDL registers |
| **[Delta](../../projects/components/fabric-gen-ip/delta)** | In progress | AXI-Stream crossbar generator (all AXIS4/5 flavors) |
| **[APB Crossbar](../../projects/components/fabric-gen-ip/apbx-xbar)** | Ready | M×N APB interconnect |
| **[pumice](../../projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2)** | Ready (at rest) | DDR2/LPDDR2 controller, board-validated on Nexys A7 |
| **[scoria](../../projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3)** | In progress | DDR3/LPDDR3 controller, simulation-verified, board campaign ongoing |
| **[andesite](../../projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4)** | Planned | DDR4/LPDDR4 controller (directory baseline) |
| **[granite / gabbro / diorite](../../projects/components/mem-ctrl-ip/product-ip)** | Planned | Production-shaped controller tops wrapping the research rocks |
| **[Reed-Solomon](../../projects/components/ecc-ip/reed-solomon)** | Ready | RS(n,k) over GF(2^m); 1.0, loopback-validated |
| **[BCH](../../projects/components/ecc-ip/bch)** | Ready | Binary BCH codec; 1.0, Genesys-2 board-validated |
| **[kestrel](../../projects/components/riscv-ip/kestrel-rv32i)** | Ready | RV32I single-cycle core (rv32ui + riscv-formal 42/42) |
| **[falcon suite rungs](../../projects/components/riscv-ip)** | Planned | merlin / peregrine / gyrfalcon / garuda RISC-V ladder |
| **[HIVE](../../projects/components/riscv-ip/hive-serv)** | Planned | Distributed RISC-V control (VexRiscv + 16 SERV cores) |
| **[amber](../../projects/components/cache-ip/amber-mesi-l1)** | In progress | Blocking MESI snoopy L1 (gemstone family) |
| **[cache-ip rungs](../../projects/components/cache-ip)** | Planned | jet (MSHR L1) · basalt (MOESI L2) · onyx (ACE CCU) |
| **[dfx-ip](../../projects/components/dfx-ip)** | Planned | House debug port: jtag-tap, jtag-axil-agent, riscv-debug |
| **[Retro Legacy](../../projects/components/retro_legacy_blocks)** | Ready | HPET, PIC, PIT, RTC, UART, GPIO, etc. |
| **[Converters](../../projects/components/utility-ip/converters)** | Ready | UART-to-AXI4-Lite, protocol conversion |

### Verification
- **[Common Tests](../../val/common)** - Unit tests for common modules
- **[AMBA Tests](../../val/amba)** - Protocol compliance tests
- **[CocoTB Framework](../../bin/TBClasses)** - Reusable testbench infrastructure

### Tools
- **[RTL Generators](../../bin/rtl_generators)** - Math circuits, floating-point modules
- **[Documentation Tools](../../bin)** - md_to_docx.py, header management

---

## Progressive Learning Approach

### Level 1: Common Building Blocks (Foundation)

**Location:** [`rtl/common/`](../../rtl/common) | **Documentation:** [Full Index](rtl-common/index.md) | [AI Guide](../../rtl/common/CLAUDE.md)

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

**Tests:** [`val/common/`](../../val/common) - Every module has comprehensive CocoTB tests

---

### Level 2: AMBA Protocol Infrastructure

**Location:** [`rtl/amba/`](../../rtl/amba) | **Documentation:** [Full Index](rtl-amba/index.md) | [AI Guide](../../rtl/amba/CLAUDE.md)

Apply common building blocks to implement industry-standard protocols (**124 modules**):

#### APB (Advanced Peripheral Bus)
- **[APB Masters](../../rtl/amba/apb4)** - Command/response interfaces with FIFO buffering
- **[APB Slaves](../../rtl/amba/apb4)** - Register interfaces with address decoding
- **APB Interconnect** - Multi-master/multi-slave crossbar (the `rtl/integ_*` examples were retired in `41e587b1`; see `projects/components/fabric-gen-ip/apbx-xbar/`)
- **[APB Bridges](../../rtl/amba/apb4)** - Protocol conversion, CDC

**Example:** APB register slave demonstrates parameter-driven design
```systemverilog
apb4_slave #(
    .ADDR_WIDTH(12),
    .DATA_WIDTH(32)
) u_apb4_slave (
    .pclk, .presetn, .paddr, .psel, .penable, .pwrite,
    .pwdata, .pready, .prdata, .pslverr
);
```

#### AXI4 Full Protocol
- **[AXI4 Masters](../../rtl/amba/axi4)** - Read/write with dual skid buffers
- **[AXI4 Slaves](../../rtl/amba/axi4)** - Response generation, address decoding
- **[AXI4 Infrastructure](../../rtl/amba/gaxi)** - FIFOs, skid buffers, arbiters
- **[Monitoring](../../rtl/amba/axi4)** - Protocol compliance checkers

#### AXI4-Lite (Simplified Register Interface)
- **[AXI4-Lite Masters](../../rtl/amba/axil4)** - Register-optimized masters
- **[AXI4-Lite Slaves](../../rtl/amba/axil4)** - Configuration registers
- **[Protocol Bridges](../../projects/components/utility-ip/converters/rtl/)** - APB ↔ AXI-Lite conversion (converters component)

#### AXI4-Stream (High-Throughput Data)
- **[Stream Masters/Slaves](../../rtl/amba/axis4/)** - Streaming interfaces
- **[Flow Control](../../rtl/amba/axis4/)** - Backpressure, buffering
- **[Sideband Support](../../rtl/amba/axis4/)** - TID, TDEST, TUSER, TSTRB

#### Shared Infrastructure
- **[GAXI Buffers](../../rtl/amba/gaxi)** - Generic skid buffers, FIFOs, CDC
- **[Monitors](../../rtl/amba/shared)** - Transaction monitoring, performance analysis
- **[Arbiters](../../rtl/amba/shared)** - Advanced arbitration for monitor buses

**Tests:** [`val/amba/`](../../val/amba) - Protocol compliance and integration tests

---

### Level 3: Integration Examples

**Locations:** retired in `41e587b1` — the integration examples are gone; the crossbar lives in `projects/components/fabric-gen-ip/apbx-xbar/`

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

---

### Level 4: Production Components

**Location:** [`projects/components/`](../../projects/components) | **Documentation:** [Component Index](projects/index.md)

Build complete, production-ready peripherals for FPGA deployment (**25+ components**):

#### DMA Engines

| Component | Status | Description |
|-----------|--------|-------------|
| **[STREAM](../../projects/components/dma-ip/stream)** | Ready | Tutorial DMA with 8 channels, scatter-gather, APB config |
| **[RAPIDS](../../projects/components/dma-ip/rapids)** | Ready | Advanced DMA with alignment fixup, network TX/RX, credit flow (qualified 2026-10-11) |

#### Interconnect and Bridges

| Component | Status | Description |
|-----------|--------|-------------|
| **[APB Crossbar](../../projects/components/fabric-gen-ip/apbx-xbar)** | Ready | Parametric M×N APB interconnect with round-robin arbitration |
| **[Bridge](../../projects/components/fabric-gen-ip/bridge)** | Ready | Generated AMBA 3/4/5 + Wishbone-4 protocol bridges, width converters, CDC |
| **[Delta](../../projects/components/fabric-gen-ip/delta)** | In progress | AXI-Stream crossbar generator — Python-generated flat M×N crossbars in all AXIS4/5 flavors |
| **[Converters](../../projects/components/utility-ip/converters)** | Ready | UART-to-AXI4-Lite, protocol conversion bridges |

#### Memory Controllers

| Component | Status | Description |
|-----------|--------|-------------|
| **[pumice](../../projects/components/mem-ctrl-ip/research-ip/pumice-ddr2-lpddr2)** | Ready (at rest) | DDR2/LPDDR2 controller, board-validated on Nexys A7 |
| **[scoria](../../projects/components/mem-ctrl-ip/research-ip/scoria-ddr3-lpddr3)** | In progress | DDR3/LPDDR3 controller, simulation-verified; board bring-up ongoing |
| **[andesite](../../projects/components/mem-ctrl-ip/research-ip/andesite-ddr4-lpddr4)** | Planned | DDR4/LPDDR4 directory baseline (structure only) |
| **[product tops](../../projects/components/mem-ctrl-ip/product-ip)** (granite / gabbro / diorite) | Planned | Production-shaped tops wrapping the research rocks (scaffolds) |

#### Error Correction (ECC)

| Component | Status | Description |
|-----------|--------|-------------|
| **[Reed-Solomon](../../projects/components/ecc-ip/reed-solomon)** | Ready | RS(n,k) over GF(2^m); riBM/Euclidean solvers, AXIS/AXI4 adapters; 1.0, hardware-loopback-validated |
| **[BCH](../../projects/components/ecc-ip/bch)** | Ready | Binary BCH encoder/decoder on the shared GF(2^m) layer; 1.0, Genesys-2 board-validated |

#### RISC-V Falcon Suite

| Component | Status | Description |
|-----------|--------|-------------|
| **[kestrel](../../projects/components/riscv-ip/kestrel-rv32i)** | Ready | RV32I single-cycle core — rv32ui 42/42 spike lockstep, riscv-formal 42/42 |
| **[merlin / peregrine / gyrfalcon / garuda](../../projects/components/riscv-ip)** | Planned | The ladder: 5-stage → advanced in-order → OoO capstone (+A atomics) → OoO + FPU |
| **[HIVE](../../projects/components/riscv-ip/hive-serv)** | Planned | Distributed RISC-V control (VexRiscv + 16 SERV monitors) |

#### Cache Coherence (gemstone family)

| Component | Status | Description |
|-----------|--------|-------------|
| **[amber](../../projects/components/cache-ip/amber-mesi-l1)** | In progress | Blocking MESI snoopy L1 (HAS/MAS v1.0; RTL landing) |
| **[jet / basalt / onyx](../../projects/components/cache-ip)** | Planned | Lockup-free MESI L1 (MSHR) · MOESI L2 · ACE coherence manager (CCU) |

#### Debug / DFX

| Component | Status | Description |
|-----------|--------|-------------|
| **[dfx-ip](../../projects/components/dfx-ip)** | Planned (scaffold) | House debug port: jtag-tap transport, jtag-axil-agent config poke, riscv-debug override plane |

#### Retro Legacy Blocks

**Status:** Production Ready | **Location:** [`projects/components/retro_legacy_blocks/`](../../projects/components/retro_legacy_blocks)

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

**Documentation:** [PRD](../../projects/components/retro_legacy_blocks/PRD.md)

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
├── rtl/                          # RTL source code (~390 modules)
│   ├── common/                   # ~57 building blocks (counters, FIFOs, arbiters, etc.)
│   ├── math/                     # ~170 arithmetic modules (integer + FP)
│   ├── cdc/                      # Clock-domain-crossing library
│   ├── amba/                     # ~160 AMBA protocol modules
│   │   ├── apb4/ apb5/          # APB protocol generations
│   │   ├── axil4/ axil5/        # AXI4-Lite / AXI5-Lite
│   │   ├── axi4/ axi5/          # AXI full + AMBA5
│   │   ├── axis4/ axis5/        # AXI-Stream
│   │   ├── ace/                 # AXI Coherency Extensions
│   │   ├── wb4/                 # Wishbone-4
│   │   ├── gaxi/                # Generic AXI infrastructure
│   │   ├── monitor/             # Transaction monitors + MonBus groups
│   │   └── shared/              # Shared observation utilities
│
├── projects/                     # Component projects (25+)
│   ├── components/
│   │   ├── dma-ip/              # STREAM / RAPIDS DMA engines (Done)
│   │   ├── fabric-gen-ip/       # Bridge, APB crossbar, Delta AXIS-xbar generator
│   │   ├── mem-ctrl-ip/         # research rocks (pumice/scoria/andesite) + product tops
│   │   ├── ecc-ip/              # Reed-Solomon + BCH (1.0, board-validated)
│   │   ├── riscv-ip/            # falcon suite (kestrel Done) + hive-serv
│   │   ├── cache-ip/            # gemstone coherence family (amber in progress)
│   │   ├── dfx-ip/              # debug-port scaffolds (jtag-tap / jtag-axil-agent / riscv-debug)
│   │   ├── noc-ip/              # future NoC draft spec (delta_spec; no RTL)
│   │   ├── compute-eng-ip/      # retired (empty — hive re-homed to riscv-ip 2026-10-10)
│   │   ├── retro_legacy_blocks/ # 9 legacy peripherals
│   │   └── utility-ip/          # Converters, misc
│   ├── fpga-systems/            # Board harnesses (Nexys A7, Genesys 2) + boards/
│   └── asic-trials/             # timing_characterization
│
├── val/                          # Validation/Test suites
│   ├── common/                  # Common module tests
│   └── amba/                    # AMBA protocol tests
│
├── formal/                       # Formal verification (SymbiYosys proof areas)
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
│   │   ├── rtl-common/           # Common library docs
│   │   ├── rtl-amba/             # AMBA library docs
│   │   ├── CocoTBFramework/     # Framework docs
│   │   └── projects/            # Component docs
│   └── DOCUMENTATION_INDEX.md   # Master doc index
│
├── CLAUDE.md                     # Repository AI guide
└── README.md                     # Repo-root landing page (component lists kept in sync with this overview)
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
pytest val/amba/test_apb4_slave.py -v

# Run only basic tests
pytest val/amba/test_apb4_slave.py -v -m basic
```

#### Level 3: Test APB Crossbar Integration
```bash
# Run 2-to-4 crossbar test
pytest projects/components/fabric-gen-ip/apbx-xbar/dv/tests/test_apbx_xbar_2to4.py -v -k "2to4"
```

#### Level 4: Test Retro Legacy Block Component
```bash
# Run HPET tests from Retro Legacy Blocks collection
pytest projects/components/retro_legacy_blocks/dv/tests/hpet/ -v

# Run specific test
pytest projects/components/retro_legacy_blocks/dv/tests/test_apb4_hpet.py -v
```

---

## Learning Resources

### Documentation by Level

**Level 1 - Common Modules:**
- [Common Library PRD](rtl-common/index.md) - Requirements and specifications
- [Common CLAUDE Guide](../../rtl/common/CLAUDE.md) - AI-assisted development
- [Common Tests](../../val/common) - Example test patterns

**Level 2 - AMBA Protocols:**
- [AMBA Infrastructure PRD](rtl-amba/index.md) - Protocol specifications
- [AMBA CLAUDE Guide](../../rtl/amba/CLAUDE.md) - Implementation patterns
- [AMBA Tests](../../val/amba) - Protocol compliance tests

**Level 3 - Components:**
- [Component Index](projects/index.md) - All components
- [Component Overview](projects/overview.md) - Design patterns
- [Retro Legacy Blocks](../../projects/components/retro_legacy_blocks/README.md) - Legacy peripheral collection
- [HPET Specification](../../projects/components/retro_legacy_blocks/docs/hpet_mas/hpet_mas_index.md) - Complete HPET guide

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
- **~160 AMBA Modules** - APB, AXI4/5, AXI-Lite, AXI-Stream, ACE, Wishbone-4
- **25+ Production Components** - DMA engines, interconnect generators, ECC, memory controllers, RISC-V cores, caches
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
- **STREAM / RAPIDS DMA** - both qualified Done 2026-10-11 (RAPIDS beats characterized on Genesys 2)
- **Bridge / APB crossbar** - Done; AMBA 3/4/5 + WB4 bridge generator, M×N APB xbar
- **ECC codecs** - Reed-Solomon + BCH 1.0, loopback-validated on Nexys A7 and Genesys 2
- **Retro Legacy Blocks** - 9 peripherals with MAS documentation
- **kestrel RV32I core** - Done (rv32ui 42/42 spike lockstep, riscv-formal 42/42)
- **Floating-Point** - FP32 FMA, additional converters

### Near-Term
- **Delta** AXI-Stream crossbar generator - DV suite in progress (the NoC mesh draft is archived at noc-ip/delta_spec, unimplemented)
- **cache-ip gemstone family** - amber RTL qualification, then jet / onyx / basalt
- **scoria DDR3/LPDDR3** - board bring-up campaign
- **HIVE** distributed RISC-V control
- **dfx-ip** debug-port specs (jtag-tap, jtag-axil-agent, riscv-debug)
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
