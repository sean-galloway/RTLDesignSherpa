# Miscellaneous Components

**Version:** 1.2
**Last Updated:** 2025-11-11
**Status:** ✅ Active - Four complete utility modules

---

## Overview

The `misc/` component area contains utility modules and adapters that don't fit into larger subsystems but are useful for system integration. These are production-quality, reusable building blocks for common design patterns.

**Design Philosophy:**
- **Single-Purpose Modules:** Each module solves one specific integration problem
- **Production Quality:** Fully tested and documented
- **Reusable:** Technology-agnostic, parameterized implementations
- **Standard Interfaces:** Use industry-standard protocols (AXI4, APB, etc.)

---

## Components

### AXI4 Slave ROM

**Status:** ✅ Complete

**Description:**
Read-only memory (ROM) with AXI4 read interface. Combines `axi4_slave_rd` protocol handler with `simple_rom` storage backend.

**Files:**
- `rtl/axi4_slave_rom.sv` - AXI4 ROM wrapper implementation

**Key Features:**
- AXI4 read-only slave interface (AR + R channels only)
- Parameterizable data width, address width, ID width
- FPGA block RAM inference with cross-vendor synthesis attributes
- Optional initialization from file (hex format)
- Single-cycle ROM access latency
- Burst support via `axi4_slave_rd` handler

**Applications:**
- Boot ROM for embedded processors
- Configuration data storage
- Lookup tables (LUTs)

---

### AXI4 Read Pattern Generator (DMA Test)

**Status:** ✅ Complete

**Description:**
AXI4 read slave that generates pseudo-random patterns using 32-bit LFSR and computes CRC-32 for DMA validation. Used with companion write CRC checker to verify data integrity across DMA transfers.

**Files:**
- `rtl/axi4_slave_rd_pattern_gen.sv` - Read pattern generator with CRC

**Key Features:**
- 32-bit LFSR pattern generator (maximal length sequence)
- Pattern replication for wider AXI data widths (64, 128, 256, 512-bit)
- CRC-32 Ethernet computation on LFSR output
- Synchronous reset control for test sequences
- Beat counter for debug
- CRC value output for UART readback

**Architecture:**
```
LFSR (32-bit) → Replicate → AXI R data
      ↓
   CRC-32 → read_crc_value (output)
```

**Test Control Interface:**
- `crc_lfsr_reset` - Pulse to start new test sequence
- `read_crc_value[31:0]` - Current CRC for validation
- `read_crc_valid` - CRC valid flag
- `read_beat_count[31:0]` - Number of reads served

**Applications:**
- DMA characterization and validation
- Data path integrity testing
- FPGA streaming performance measurement

**Companion Module:** `axi4_slave_wr_crc_check.sv`

---

### AXI4 Write CRC Checker (DMA Test)

**Status:** ✅ Complete

**Description:**
AXI4 write slave that computes CRC-32 on received data for DMA validation. Companion to read pattern generator - receives DMA writes and computes CRC for comparison.

**Files:**
- `rtl/axi4_slave_wr_crc_check.sv` - Write CRC checker

**Key Features:**
- Extracts 32-bit slice from AXI write data
- CRC-32 Ethernet computation on write data
- Synchronous reset control for test sequences
- Beat counter for debug
- CRC value output for UART readback
- Write data discarded (no storage backend)

**Architecture:**
```
AXI W data → Extract 32-bit slice → CRC-32 → write_crc_value (output)
```

**Test Control Interface:**
- `crc_reset` - Pulse to start new test sequence
- `write_crc_value[31:0]` - Current CRC for validation
- `write_crc_valid` - CRC valid flag
- `write_beat_count[31:0]` - Number of writes received

**Applications:**
- DMA data integrity validation
- Streaming data path verification
- End-to-end transfer validation

**Companion Module:** `axi4_slave_rd_pattern_gen.sv`

**Example DMA Test Flow (Python via UART):**
```python
# Reset both modules
uart.write("RESET_CRC_LFSR")

# DMA transfers
dma.read_burst(addr=pattern_gen_addr, length=10000)
dma.write_burst(addr=crc_check_addr, length=10000)

# Read CRC values via UART
read_crc = uart.read("READ_CRC_VALUE")
write_crc = uart.read("WRITE_CRC_VALUE")

# Validate
if read_crc == write_crc:
    print(f"✅ PASS: Data integrity verified (CRC=0x{read_crc:08x})")
else:
    print(f"❌ FAIL: CRC mismatch - Read=0x{read_crc:08x}, Write=0x{write_crc:08x}")
```

---

### UART to AXI4-Lite Bridge

**Status:** ✅ Complete

**Description:**
UART command-line interface to AXI4-Lite memory-mapped peripherals. Parses ASCII commands received via UART and executes corresponding AXI4-Lite transactions.

**Files:**
- `rtl/uart_to_axil4/uart_axil_bridge.sv` - Main bridge (parser + AXI4-Lite master)
- `rtl/uart_to_axil4/uart_rx.sv` - UART receiver (8N1)
- `rtl/uart_to_axil4/uart_tx.sv` - UART transmitter (8N1)
- `rtl/uart_to_axil4/README.md` - Complete documentation

**Key Features:**
- Simple ASCII command protocol (human-readable)
- AXI4-Lite master interface with timing isolation
- Configurable baud rate (default: 115200)
- Single-transaction operation (read/write)
- Minimal resource usage (~300 LUTs, ~200 FFs)

**Command Protocol:**
```bash
# Write command: W <addr_hex> <data_hex>\n
W 1000 DEADBEEF
Response: OK

# Read command: R <addr_hex>\n
R 1000
Response: 0xDEADBEEF
```

**Applications:**
- Debug access to memory-mapped registers
- FPGA board bring-up and testing
- DMA control (perfect companion to pattern gen/CRC checker!)
- Low-speed peripheral control

**Integration Example:**
```systemverilog
uart_axil_bridge #(
    .AXIL_ADDR_WIDTH(32),
    .AXIL_DATA_WIDTH(32),
    .CLKS_PER_BIT(868)  // 100MHz / 115200 baud
) u_uart_bridge (
    .aclk(clk),
    .aresetn(rst_n),
    .i_uart_rx(uart_rx_pin),
    .o_uart_tx(uart_tx_pin),
    // AXI4-Lite Master interface...
);
```

**Python Control Example:**
```python
import serial

uart = serial.Serial('/dev/ttyUSB0', 115200)

# Reset DMA pattern generator CRC
uart.write(b'W 2000 00000001\n')  # Write 1 to crc_reset register
uart.readline()  # Read "OK"

# Read CRC value
uart.write(b'R 2004\n')  # Read from crc_value register
crc = uart.readline()  # e.g., "0x12345678"
```

**Timing Isolation:**
- Skid buffers on all AXI4-Lite channels
- Breaks timing paths between slow UART and fast AXI bus
- Configurable depths for high-frequency designs

**See:** `rtl/uart_to_axil4/README.md` for complete documentation

---

### AXI ROM Wrapper (Legacy Planning Doc)

**Status:** 📋 Superseded by axi4_slave_rom.sv

**Description:**
Read-only memory (ROM) with AXI4 read interface. Useful for boot code, configuration data, lookup tables, or any read-only data storage that needs AXI4 compliance.

**Key Features:**
- AXI4 read-only slave interface (AR + R channels only)
- Parameterizable data width (32, 64, 128, 256, 512 bits)
- Parameterizable depth
- FPGA block RAM inference with synthesis attributes
- Optional initialization from file (hex, bin, mem formats)
- Single-cycle read latency
- Burst support (INCR, WRAP, FIXED)

**Planned Parameters:**
```systemverilog
module axi_rom_wrapper #(
    parameter int DATA_WIDTH = 64,          // AXI data width
    parameter int ADDR_WIDTH = 16,          // Address width (byte addressing)
    parameter int ID_WIDTH = 4,             // AXI ID width
    parameter string INIT_FILE = "none"     // Initialization file path
) (
    // AXI4 Read Interface
    input  logic                    aclk,
    input  logic                    aresetn,
    // AR channel
    input  logic [ADDR_WIDTH-1:0]   s_axi_araddr,
    input  logic [ID_WIDTH-1:0]     s_axi_arid,
    input  logic [7:0]              s_axi_arlen,
    input  logic [2:0]              s_axi_arsize,
    input  logic [1:0]              s_axi_arburst,
    input  logic                    s_axi_arvalid,
    output logic                    s_axi_arready,
    // R channel
    output logic [DATA_WIDTH-1:0]   s_axi_rdata,
    output logic [ID_WIDTH-1:0]     s_axi_rid,
    output logic [1:0]              s_axi_rresp,
    output logic                    s_axi_rlast,
    output logic                    s_axi_rvalid,
    input  logic                    s_axi_rready
);
```

**Applications:**
- Boot ROM for embedded processors
- Configuration data storage
- Lookup tables (LUTs) for algorithms
- Test pattern generators
- Calibration data storage

**Future Variants:**
- `apb_rom_wrapper` - APB interface version
- `axi_ram_wrapper` - Read/write variant with AXI4 full interface

---

## Directory Structure

```
projects/components/misc/
├── bin/                        # Utility scripts
│   └── generate_rom_init.py    # Tool to create ROM initialization files
├── dv/
│   ├── tbclasses/              # Testbench classes
│   │   └── axi_rom_tb.py       # AXI ROM testbench
│   └── tests/                  # Test runners
│       └── test_axi_rom.py     # AXI ROM test suite
├── rtl/
│   ├── axi_rom_wrapper.sv      # AXI ROM implementation
│   └── filelists/
│       └── axi_rom.f           # Filelist for synthesis
├── docs/                       # Component documentation
│   └── axi_rom_spec.md         # AXI ROM specification
├── README.md                   # This file
└── CLAUDE.md                   # AI assistance guide
```

---

## Usage Examples

### Example 1: Boot ROM for RISC-V Processor

```systemverilog
// 16KB boot ROM at 0x1000_0000
axi_rom_wrapper #(
    .DATA_WIDTH(64),
    .ADDR_WIDTH(14),        // 16KB = 2^14 bytes
    .ID_WIDTH(4),
    .INIT_FILE("boot_code.hex")
) u_boot_rom (
    .aclk            (cpu_clk),
    .aresetn         (cpu_rst_n),
    // AR channel
    .s_axi_araddr    (boot_araddr),
    .s_axi_arid      (boot_arid),
    .s_axi_arlen     (boot_arlen),
    .s_axi_arsize    (boot_arsize),
    .s_axi_arburst   (boot_arburst),
    .s_axi_arvalid   (boot_arvalid),
    .s_axi_arready   (boot_arready),
    // R channel
    .s_axi_rdata     (boot_rdata),
    .s_axi_rid       (boot_rid),
    .s_axi_rresp     (boot_rresp),
    .s_axi_rlast     (boot_rlast),
    .s_axi_rvalid    (boot_rvalid),
    .s_axi_rready    (boot_rready)
);
```

### Example 2: Lookup Table for Signal Processing

```systemverilog
// 4KB sine wave lookup table
axi_rom_wrapper #(
    .DATA_WIDTH(32),
    .ADDR_WIDTH(12),        // 4KB = 2^12 bytes
    .ID_WIDTH(4),
    .INIT_FILE("sine_lut.hex")
) u_sine_lut (
    .aclk            (dsp_clk),
    .aresetn         (dsp_rst_n),
    // Connect to DSP accelerator read interface
    .s_axi_araddr    (lut_araddr),
    .s_axi_arid      (lut_arid),
    .s_axi_arlen     (lut_arlen),
    .s_axi_arsize    (lut_arsize),
    .s_axi_arburst   (lut_arburst),
    .s_axi_arvalid   (lut_arvalid),
    .s_axi_arready   (lut_arready),
    .s_axi_rdata     (lut_rdata),
    .s_axi_rid       (lut_rid),
    .s_axi_rresp     (lut_rresp),
    .s_axi_rlast     (lut_rlast),
    .s_axi_rvalid    (lut_rvalid),
    .s_axi_rready    (lut_rready)
);
```

---

## Adding New Components

When adding new miscellaneous components, follow these guidelines:

### 1. Component Criteria

A component belongs in `misc/` if it:
- ✅ Solves a common integration problem
- ✅ Is reusable across multiple projects
- ✅ Doesn't fit into existing component categories
- ✅ Is production-quality (tested, documented)
- ✅ Uses standard interfaces (AXI4, APB, etc.)

Examples of appropriate components:
- Protocol wrappers (ROM/RAM with standard interfaces)
- Common adapters (clock domain crossing, width conversion)
- Utility blocks (pattern generators, checkers)
- Glue logic patterns (address decoders, mux trees)

### 2. Directory Structure per Component

Each component should have:

```
rtl/
├── {component_name}.sv         # Main RTL implementation
├── {component_name}_pkg.sv     # Package (if needed)
└── filelists/
    └── {component_name}.f      # Synthesis filelist

dv/
├── tbclasses/
│   └── {component_name}_tb.py  # Testbench class
└── tests/
    └── test_{component_name}.py # Test runner

docs/
└── {component_name}_spec.md    # Component specification
```

### 3. Naming Convention

- **RTL modules:** `{interface}_{type}_wrapper`
  - Examples: `axi_rom_wrapper`, `apb_ram_wrapper`
- **Testbench classes:** `{ComponentName}TB`
  - Examples: `AXIRomTB`, `APBRamTB`
- **Test files:** `test_{component_name}.py`
  - Examples: `test_axi_rom.py`, `test_apb_ram.py`

### 4. Documentation Requirements

Each component must have:
- **Specification:** `docs/{component_name}_spec.md`
  - Purpose and features
  - Interface description
  - Parameter definitions
  - Timing diagrams
  - Usage examples
- **Inline Comments:** RTL self-documenting
- **Test Documentation:** Test methodology in test file headers

---

## Testing

```bash
# Run all misc component tests
pytest projects/components/misc/dv/tests/ -v

# Run specific component tests
pytest projects/components/misc/dv/tests/test_axi_rom.py -v

# Run with waveforms
WAVES=1 pytest projects/components/misc/dv/tests/test_axi_rom.py -v
gtkwave logs/test_axi_rom.vcd
```

---

## Future Components (Candidates)

Potential future additions to `misc/`:

| Component | Description | Priority |
|-----------|-------------|----------|
| `axi_ram_wrapper` | AXI4 read/write RAM | High |
| `apb_rom_wrapper` | APB read-only ROM | High |
| `apb_ram_wrapper` | APB read/write RAM | Medium |
| `axi_pattern_gen` | AXI4 test pattern generator | Medium |
| `axi_monitor_lite` | Lightweight AXI4 transaction monitor | Medium |
| `async_fifo_wrapper` | Clock domain crossing FIFO with standard interface | Medium |
| `address_decoder` | Parameterizable address decode logic | Low |
| `register_slice` | AXI4 register slice for timing closure | Low |

---

## Design Standards

All components in `misc/` must follow repository standards:

### RTL Standards
- ✅ Use reset macros (`ALWAYS_FF_RST`)
- ✅ Add FPGA synthesis attributes for memories
- ✅ Use modern array syntax `[DEPTH]` not `[0:DEPTH-1]`
- ✅ Parameterized and configurable
- ✅ Lint-clean (Verilator)

### Testbench Standards
- ✅ TB classes in `dv/tbclasses/` (NOT in test files)
- ✅ Implement three mandatory methods (setup/assert/deassert)
- ✅ Inherit from `TBBase`
- ✅ 100% test pass rate target
- ✅ Comprehensive coverage

### Documentation Standards
- ✅ Component specification in `docs/`
- ✅ Usage examples in README
- ✅ Inline RTL comments
- ✅ Test methodology documented

**📖 See:**
- Root `/CLAUDE.md` - Repository-wide standards
- `/GLOBAL_REQUIREMENTS.md` - Mandatory requirements
- `projects/components/CLAUDE.md` - Component-area standards

---

## Quick Reference

```bash
# Create new component structure
cd projects/components/misc
mkdir -p rtl/{component_name}/filelists
mkdir -p dv/tbclasses/{component_name}
mkdir -p dv/tests/{component_name}
mkdir -p docs

# Lint RTL
verilator --lint-only rtl/{component_name}.sv

# Run tests
pytest dv/tests/test_{component_name}.py -v

# View documentation
cat docs/{component_name}_spec.md
```

---

## Contributing

When adding components to `misc/`:

1. **Check Existing Components:** Ensure functionality doesn't already exist
2. **Follow Standards:** Use repository RTL/testbench standards
3. **Document Thoroughly:** Specification + usage examples
4. **Test Comprehensively:** 100% pass rate, good coverage
5. **Update README:** Add component to list above

---

## Resources

### Internal Documentation
- `/CLAUDE.md` - Repository standards
- `/GLOBAL_REQUIREMENTS.md` - Mandatory requirements
- `projects/components/CLAUDE.md` - Component area standards
- `bin/CocoTBFramework/` - Testbench framework

### External References
- **AXI4 Protocol:** ARM IHI0022E (AMBA AXI and ACE Protocol Specification)
- **APB Protocol:** ARM IHI0024C (AMBA APB Protocol Specification)
- **Verilator:** https://verilator.org/guide/latest/

---

**Version:** 1.2
**Last Updated:** 2025-11-11
**Maintained By:** RTL Design Sherpa Project

**Status:** Active collection of utility components. Four complete modules:
- ✅ `axi4_slave_rom.sv` - AXI4 ROM wrapper
- ✅ `axi4_slave_rd_pattern_gen.sv` - DMA test pattern generator with CRC
- ✅ `axi4_slave_wr_crc_check.sv` - DMA test CRC checker
- ✅ `uart_to_axil4/` - UART to AXI4-Lite bridge (debug/control interface)

---

## Navigation

- **← Back to Components:** [`../README.md`](../README.md)
- **Repository Guide:** [`/CLAUDE.md`](../../../CLAUDE.md)
- **Global Requirements:** [`/GLOBAL_REQUIREMENTS.md`](../../../GLOBAL_REQUIREMENTS.md)
