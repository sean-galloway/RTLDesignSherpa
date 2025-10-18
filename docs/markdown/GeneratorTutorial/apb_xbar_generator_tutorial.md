# APB Crossbar Generator Tutorial

**Version:** 1.0
**Last Updated:** 2025-10-14
**Difficulty:** Intermediate

---

## Table of Contents

1. [Introduction](#introduction)
2. [Prerequisites](#prerequisites)
3. [Quick Start](#quick-start)
4. [Understanding the Generator](#understanding-the-generator)
5. [Command-Line Usage](#command-line-usage)
6. [Generated Code Structure](#generated-code-structure)
7. [Customizing Generated Code](#customizing-generated-code)
8. [Integration Workflow](#integration-workflow)
9. [Advanced Topics](#advanced-topics)
10. [Troubleshooting](#troubleshooting)
11. [Best Practices](#best-practices)

---

## Introduction

### What is RTL Generation?

**RTL Generation** is the process of programmatically creating hardware description language (HDL) code using scripts or tools. Instead of manually writing repetitive SystemVerilog modules, you define patterns and let a generator create optimized, consistent code.

### Why Use RTL Generators?

**Benefits:**
- ✅ **Consistency**: All generated modules follow same coding style
- ✅ **Scalability**: Easy to create MxN configurations without copy-paste
- ✅ **Maintainability**: Fix bugs in generator, regenerate all modules
- ✅ **Productivity**: Generate in seconds what would take hours manually
- ✅ **Correctness**: Reduce human error in repetitive code

**When to Use:**
- Parameterized modules with many configurations
- Repetitive structures (crossbars, muxes, arbiters)
- System-level integration with many instances
- Design space exploration

**When NOT to Use:**
- Simple modules with few parameters
- Complex custom logic
- One-off designs

### The APB Crossbar Generator

The APB crossbar generator (`apb_xbar_generator.py`) creates scalable APB interconnects from 1x1 to 16x16 masters/slaves.

**Generated Crossbar Capabilities:**
- M masters to N slaves (1 ≤ M, N ≤ 16)
- Round-robin arbitration per slave
- Address decoding with 64KB regions
- Full APB5 protocol support
- Parameterizable address/data widths

**Example: 2x4 Crossbar**
```
2 Masters ──┐
            ├──▶ Crossbar ──┐
            │                ├──▶ 4 Slaves
            │                │
            └────────────────┘
```

---

## Prerequisites

### Required Knowledge

- **SystemVerilog**: Basic module syntax, parameters, interfaces
- **Python**: Basic programming (functions, f-strings, file I/O)
- **APB Protocol**: Two-phase transactions (SETUP, ACCESS)
- **Command Line**: Running Python scripts, file navigation

### Required Tools

```bash
# Verify Python installation
python3 --version  # Should be 3.7+

# Verify repository structure
ls rtl/amba/apb/xbar/
# Should see: generate_xbars.py, README.md, *.sv files

ls bin/rtl_generators/amba/
# Should see: apb_xbar_generator.py
```

### Recommended Reading

Before starting this tutorial:
1. **APB Protocol**: ARM IHI0024 AMBA APB Specification
2. **Crossbar Architecture**: `docs/markdown/RTLAmba/apb/apb_crossbar.md`
3. **Repository Guide**: `/CLAUDE.md` (section on rtl/amba/)

---

## Quick Start

### Generate Your First Crossbar

**Step 1: Navigate to Generator Directory**
```bash
cd rtl/amba/apb/xbar
```

**Step 2: Generate Standard Crossbars**
```bash
python generate_xbars.py --all
```

Output:
```
Generating standard APB crossbar variants...

Generating 1-to-1 crossbar...
  ✓ apb_xbar_1to1.sv written (150 lines)

Generating 2-to-1 crossbar...
  ✓ apb_xbar_2to1.sv written (280 lines)

Generating 1-to-4 crossbar...
  ✓ apb_xbar_1to4.sv written (520 lines)

Generating 2-to-4 crossbar...
  ✓ apb_xbar_2to4.sv written (850 lines)

All crossbars generated successfully!
```

**Step 3: Verify Generated Files**
```bash
ls -lh *.sv
# Should see: apb_xbar_1to1.sv, apb_xbar_2to1.sv, apb_xbar_1to4.sv, apb_xbar_2to4.sv
```

**Step 4: Run Tests**
```bash
cd ../../../../val/integ_amba
pytest test_apb_xbar_1to1.py -v
```

**Congratulations!** You've successfully generated and verified your first APB crossbar.

---

## Understanding the Generator

### Generator Architecture

```
┌─────────────────────────────────────────┐
│  apb_xbar_generator.py                  │
│                                         │
│  ┌───────────────────────────────────┐ │
│  │ generate_apb_xbar(M, N, ...)      │ │
│  │                                   │ │
│  │  ┌─────────────────────────────┐ │ │
│  │  │ 1. Generate Module Header   │ │ │
│  │  │    - Parameters             │ │ │
│  │  │    - Ports (M masters, N    │ │ │
│  │  │      slaves)                │ │ │
│  │  └─────────────────────────────┘ │ │
│  │                                   │ │
│  │  ┌─────────────────────────────┐ │ │
│  │  │ 2. Generate Internal        │ │ │
│  │  │    Signals                  │ │ │
│  │  │    - cmd/rsp buses          │ │ │
│  │  │    - Address decode         │ │ │
│  │  │    - Arbitration            │ │ │
│  │  └─────────────────────────────┘ │ │
│  │                                   │ │
│  │  ┌─────────────────────────────┐ │ │
│  │  │ 3. Instantiate apb_slave    │ │ │
│  │  │    modules (M instances)    │ │ │
│  │  └─────────────────────────────┘ │ │
│  │                                   │ │
│  │  ┌─────────────────────────────┐ │ │
│  │  │ 4. Generate Crossbar Logic  │ │ │
│  │  │    - Address decode         │ │ │
│  │  │    - Arbitration using      │ │ │
│  │  │      arbiter_round_robin    │ │ │
│  │  │    - Response routing       │ │ │
│  │  └─────────────────────────────┘ │ │
│  │                                   │ │
│  │  ┌─────────────────────────────┐ │ │
│  │  │ 5. Instantiate apb_master   │ │ │
│  │  │    modules (N instances)    │ │ │
│  │  └─────────────────────────────┘ │ │
│  └───────────────────────────────────┘ │
│                                         │
│  Returns: Complete SystemVerilog code   │
└─────────────────────────────────────────┘
```

### Code Generation Strategy

The generator uses **template-based generation** with Python f-strings:

**Example: Generating Master Ports**
```python
# For each master (0 to M-1)
for m in range(M):
    code += f"""
    // Master {m} APB interface
    input  logic                  m{m}_apb_PSEL,
    input  logic                  m{m}_apb_PENABLE,
    input  logic [ADDR_WIDTH-1:0] m{m}_apb_PADDR,
    // ... more ports
"""
```

**Result for M=2:**
```systemverilog
// Master 0 APB interface
input  logic                  m0_apb_PSEL,
input  logic                  m0_apb_PENABLE,
input  logic [ADDR_WIDTH-1:0] m0_apb_PADDR,

// Master 1 APB interface
input  logic                  m1_apb_PSEL,
input  logic                  m1_apb_PENABLE,
input  logic [ADDR_WIDTH-1:0] m1_apb_PADDR,
```

### Generator Logic Flow

**1. Parameter Validation**
```python
assert 1 <= num_masters <= 16, "Masters must be 1-16"
assert 1 <= num_slaves <= 16, "Slaves must be 1-16"
```

**2. Calculate Derived Values**
```python
slave_addr_bits = max(1, math.ceil(math.log2(N)))
# Example: 4 slaves → 2 bits, 8 slaves → 3 bits
```

**3. Generate Module Structure**
- Module header with parameters
- Port list (masters + slaves)
- Internal signal declarations
- apb_slave instantiations
- Crossbar logic (address decode, arbitration)
- apb_master instantiations

**4. Handle Special Cases**
- **M=1, N=1**: Simple passthrough
- **M>1, N=1**: Arbitration only
- **M=1, N>1**: Address decode only
- **M>1, N>1**: Full crossbar (arbitration + decode)

---

## Command-Line Usage

### Basic Syntax

```bash
python generate_xbars.py [OPTIONS]
```

### Common Options

| Option | Description | Example |
|--------|-------------|---------|
| `--all` | Generate all standard variants (1to1, 2to1, 1to4, 2to4) | `python generate_xbars.py --all` |
| `--masters M` | Number of masters (1-16) | `python generate_xbars.py --masters 3` |
| `--slaves N` | Number of slaves (1-16) | `python generate_xbars.py --slaves 8` |
| `--base-addr ADDR` | Base address (hex or decimal) | `python generate_xbars.py --base-addr 0x40000000` |
| `--addr-width W` | Address bus width (16-64) | `python generate_xbars.py --addr-width 32` |
| `--data-width W` | Data bus width (8, 16, 32, 64) | `python generate_xbars.py --data-width 64` |
| `--output FILE` | Output file path | `python generate_xbars.py --output custom.sv` |

### Example Commands

**Example 1: Standard Crossbars**
```bash
# Generate all standard variants
python generate_xbars.py --all
```

**Example 2: Custom 3x8 Crossbar**
```bash
# 3 masters, 8 slaves
python generate_xbars.py --masters 3 --slaves 8
```
Output: `apb_xbar_3to8.sv`

**Example 3: Custom Base Address**
```bash
# 2 masters, 4 slaves, base address 0x80000000
python generate_xbars.py --masters 2 --slaves 4 --base-addr 0x80000000
```

**Example 4: Wide Data Bus**
```bash
# 1 master, 4 slaves, 64-bit data bus
python generate_xbars.py --masters 1 --slaves 4 --data-width 64
```

**Example 5: Custom Output File**
```bash
# Save to specific location
python generate_xbars.py --masters 4 --slaves 4 --output ../../custom/my_xbar.sv
```

### Using the Python API Directly

You can also use the generator programmatically:

```python
import sys
sys.path.append('../../../bin/rtl_generators/amba')
from apb_xbar_generator import generate_apb_xbar

# Generate 3x8 crossbar
code = generate_apb_xbar(
    num_masters=3,
    num_slaves=8,
    base_addr=0x80000000,
    addr_width=32,
    data_width=32
)

# Save to file
with open('apb_xbar_3to8.sv', 'w') as f:
    f.write(code)

print("Generated apb_xbar_3to8.sv")
```

---

## Generated Code Structure

### Module Template

Every generated crossbar follows this structure:

```systemverilog
`timescale 1ns / 1ps

// M-to-N APB crossbar with address decoding and arbitration
// M masters to N slaves using apb_slave and apb_master modules
//
// Address Map (same for all masters):
//   Slave 0: [BASE_ADDR + 0x00000, BASE_ADDR + 0x0FFFF]
//   Slave 1: [BASE_ADDR + 0x10000, BASE_ADDR + 0x1FFFF]
//   ...

module apb_xbar_MtoN #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter int STRB_WIDTH = DATA_WIDTH / 8,
    parameter logic [ADDR_WIDTH-1:0] BASE_ADDR = 32'hXXXXXXXX
) (
    // Clock and Reset
    input  logic pclk,
    input  logic presetn,

    // Master Interfaces (M instances)
    input  logic m0_apb_PSEL,
    // ... (all M master ports)

    // Slave Interfaces (N instances)
    output logic s0_apb_PSEL,
    // ... (all N slave ports)
);

    // ========================================
    // Internal Signals
    // ========================================

    // Command/Response interfaces for each master
    logic m0_cmd_valid, m0_cmd_ready;
    // ... (M masters worth)

    // Command/Response interfaces for each slave
    logic s0_cmd_valid, s0_cmd_ready;
    // ... (N slaves worth)

    // Address decode signals
    logic m0_addr_in_range;
    logic [SLAVE_ADDR_BITS-1:0] m0_slave_sel;
    // ... (M masters worth)

    // Arbitration signals (if M > 1) - using arbiter_round_robin
    logic [M-1:0] s0_arb_request;
    logic [M-1:0] s0_arb_grant;
    logic [M-1:0] s0_arb_grant_ack;
    // ... (N slaves worth)

    // ========================================
    // APB Slave Instantiations (M instances)
    // ========================================

    apb_slave #(...) u_apb_slave_m0 (...);
    // ... (M instances)

    // ========================================
    // Address Decode Logic (if N > 1)
    // ========================================

    // Decode logic for each master
    // ...

    // ========================================
    // Arbitration Logic (if M > 1)
    // ========================================

    // Per-slave round-robin arbiters
    // ...

    // ========================================
    // Command Routing
    // ========================================

    // Route commands from masters to slaves
    // ...

    // ========================================
    // Response Routing
    // ========================================

    // Route responses from slaves to masters
    // ...

    // ========================================
    // APB Master Instantiations (N instances)
    // ========================================

    apb_master #(...) u_apb_master_s0 (...);
    // ... (N instances)

endmodule : apb_xbar_MtoN
```

### Key Code Sections

**1. apb_slave Instantiation (Master Side)**
```systemverilog
apb_slave #(
    .ADDR_WIDTH (ADDR_WIDTH),
    .DATA_WIDTH (DATA_WIDTH),
    .STRB_WIDTH (STRB_WIDTH),
    .PROT_WIDTH (3)
) u_apb_slave_m0 (
    .pclk           (pclk),
    .presetn        (presetn),
    // APB interface
    .s_apb_PSEL     (m0_apb_PSEL),
    .s_apb_PENABLE  (m0_apb_PENABLE),
    .s_apb_PREADY   (m0_apb_PREADY),
    .s_apb_PADDR    (m0_apb_PADDR),
    .s_apb_PWRITE   (m0_apb_PWRITE),
    .s_apb_PWDATA   (m0_apb_PWDATA),
    .s_apb_PSTRB    (m0_apb_PSTRB),
    .s_apb_PPROT    (m0_apb_PPROT),
    .s_apb_PRDATA   (m0_apb_PRDATA),
    .s_apb_PSLVERR  (m0_apb_PSLVERR),
    // Command interface
    .cmd_valid      (m0_cmd_valid),
    .cmd_ready      (m0_cmd_ready),
    .cmd_pwrite     (m0_cmd_pwrite),
    .cmd_paddr      (m0_cmd_paddr),
    .cmd_pwdata     (m0_cmd_pwdata),
    .cmd_pstrb      (m0_cmd_pstrb),
    .cmd_pprot      (m0_cmd_pprot),
    // Response interface
    .rsp_valid      (m0_rsp_valid),
    .rsp_ready      (m0_rsp_ready),
    .rsp_prdata     (m0_rsp_prdata),
    .rsp_pslverr    (m0_rsp_pslverr)
);
```

**2. Address Decode Logic (if N > 1)**
```systemverilog
// Master 0 address decode
always_comb begin
    // Extract slave selection bits
    m0_slave_sel = m0_cmd_paddr[SLAVE_ADDR_BITS+15:16];
    // Check if address is in valid range
    m0_addr_in_range = (m0_slave_sel < N) &&
                       (m0_cmd_paddr >= BASE_ADDR) &&
                       (m0_cmd_paddr < (BASE_ADDR + (N * 'h10000)));
end
```

**3. Arbitration Logic (if M > 1) - Using Proven Arbiter Module**
```systemverilog
// Slave 0 arbitration signals
logic [M-1:0] s0_arb_request;
logic [M-1:0] s0_arb_grant;
logic [M-1:0] s0_arb_grant_ack;

// Build request vector for slave 0
always_comb begin
    for (int m = 0; m < M; m++) begin
        // Request if master valid AND addresses this slave
        s0_arb_request[m] = m_cmd_valid[m] && m_addr_in_range[m] &&
                            (m_slave_sel[m] == 0);  // For multi-slave
        // Or simply: s0_arb_request[m] = m_cmd_valid[m];  // For single slave
    end
end

// Build grant_ack vector (signals transaction complete)
always_comb begin
    for (int m = 0; m < M; m++) begin
        s0_arb_grant_ack[m] = s0_arb_grant[m] && s0_rsp_valid && s0_rsp_ready;
    end
end

// Instantiate proven round-robin arbiter
arbiter_round_robin #(
    .CLIENTS(M),
    .WAIT_GNT_ACK(1)  // Lock grant until transaction completes
) u_s0_arbiter (
    .clk        (pclk),
    .rst_n      (presetn),
    .block_arb  (1'b0),
    .request    (s0_arb_request),
    .grant_ack  (s0_arb_grant_ack),
    .grant_valid(),  // Not used
    .grant      (s0_arb_grant),
    .grant_id   (),  // Not used
    .last_grant ()   // Not used
);
```

**Note:** The generator uses the proven `arbiter_round_robin` module from `rtl/common/` instead of hand-coded arbitration. This provides:
- Validated arbitration logic (no bugs)
- Transaction locking via WAIT_GNT_ACK=1
- Automatic priority rotation
- Grant persists until grant_ack received

**4. apb_master Instantiation (Slave Side)**
```systemverilog
apb_master #(
    .ADDR_WIDTH (ADDR_WIDTH),
    .DATA_WIDTH (DATA_WIDTH),
    .STRB_WIDTH (STRB_WIDTH),
    .PROT_WIDTH (3)
) u_apb_master_s0 (
    .pclk           (pclk),
    .presetn        (presetn),
    // APB interface
    .m_apb_PSEL     (s0_apb_PSEL),
    .m_apb_PENABLE  (s0_apb_PENABLE),
    .m_apb_PREADY   (s0_apb_PREADY),
    .m_apb_PADDR    (s0_apb_PADDR),
    .m_apb_PWRITE   (s0_apb_PWRITE),
    .m_apb_PWDATA   (s0_apb_PWDATA),
    .m_apb_PSTRB    (s0_apb_PSTRB),
    .m_apb_PPROT    (s0_apb_PPROT),
    .m_apb_PRDATA   (s0_apb_PRDATA),
    .m_apb_PSLVERR  (s0_apb_PSLVERR),
    // Command interface
    .cmd_valid      (s0_cmd_valid),
    .cmd_ready      (s0_cmd_ready),
    .cmd_pwrite     (s0_cmd_pwrite),
    .cmd_paddr      (s0_cmd_paddr),
    .cmd_pwdata     (s0_cmd_pwdata),
    .cmd_pstrb      (s0_cmd_pstrb),
    .cmd_pprot      (s0_cmd_pprot),
    // Response interface
    .rsp_valid      (s0_rsp_valid),
    .rsp_ready      (s0_rsp_ready),
    .rsp_prdata     (s0_rsp_prdata),
    .rsp_pslverr    (s0_rsp_pslverr)
);
```

---

## Customizing Generated Code

### Method 1: Command-Line Parameters

**Most common customizations can be done via command line:**

```bash
# Custom address/data widths
python generate_xbars.py --masters 2 --slaves 4 \
    --addr-width 24 --data-width 16

# Custom base address
python generate_xbars.py --masters 1 --slaves 8 \
    --base-addr 0xA0000000
```

### Method 2: Modify Generator

For deeper customizations, edit `apb_xbar_generator.py`:

**Example: Change Slave Region Size**

Default: 64KB per slave (0x10000)

```python
# In apb_xbar_generator.py
# Find this line (around line 250):
SLAVE_REGION_SIZE = 0x10000  # 64KB

# Change to 256KB:
SLAVE_REGION_SIZE = 0x40000  # 256KB
```

**Example: Add Custom Parameters**

```python
# In generate_apb_xbar() function:
def generate_apb_xbar(num_masters, num_slaves, base_addr=0x10000000,
                      addr_width=32, data_width=32, output_file=None,
                      slave_region_size=0x10000):  # ← Add new parameter

    # Use it in address decode:
    code += f"""
    // Slave regions: {hex(slave_region_size)} each
    localparam SLAVE_REGION_SIZE = {slave_region_size};
    """
```

### Method 3: Post-Process Generated Code

**Sometimes it's easier to generate, then manually edit:**

```bash
# Generate base crossbar
python generate_xbars.py --masters 2 --slaves 4

# Edit generated file
vim apb_xbar_2to4.sv

# Add custom logic:
# - Performance counters
# - Debug signals
# - Custom error handling
```

**Pro tip:** Add comments to mark custom additions:
```systemverilog
// ========================================
// CUSTOM ADDITION - Performance Counters
// ========================================
logic [31:0] txn_count;
always_ff @(posedge pclk or negedge presetn) begin
    if (!presetn) txn_count <= '0;
    else if (m0_cmd_valid && m0_cmd_ready) txn_count <= txn_count + 1;
end
// END CUSTOM ADDITION
```

---

## Integration Workflow

### Step-by-Step Integration

**Step 1: Generate Crossbar**
```bash
cd rtl/amba/apb/xbar
python generate_xbars.py --masters 2 --slaves 4
# Output: apb_xbar_2to4.sv
```

**Step 2: Create Test Wrapper**

Create `rtl/integ_amba/apb_xbar/apb_xbar_2to4_wrap.sv`:

```systemverilog
module apb_xbar_2to4_wrap #(
    parameter int ADDR_WIDTH = 32,
    parameter int DATA_WIDTH = 32,
    parameter logic [ADDR_WIDTH-1:0] BASE_ADDR = 32'h1000_0000
) (
    input  logic pclk,
    input  logic presetn
);
    localparam int STRB_WIDTH = DATA_WIDTH / 8;

    // Master 0/1 interfaces (signals for CocoTB)
    logic m0_apb_PSEL, m1_apb_PSEL;
    // ... (declare all master signals)

    // Slave 0/1/2/3 interfaces (signals for CocoTB)
    logic s0_apb_PSEL, s1_apb_PSEL, s2_apb_PSEL, s3_apb_PSEL;
    // ... (declare all slave signals)

    // Instantiate crossbar
    apb_xbar_2to4 #(
        .ADDR_WIDTH (ADDR_WIDTH),
        .DATA_WIDTH (DATA_WIDTH),
        .BASE_ADDR  (BASE_ADDR)
    ) u_xbar (
        .pclk       (pclk),
        .presetn    (presetn),
        // Connect all master interfaces
        .m0_apb_PSEL    (m0_apb_PSEL),
        // ... (connect all signals)
    );

endmodule
```

**Step 3: Create CocoTB Test**

Create `val/integ_amba/test_apb_xbar_2to4.py`:

```python
import cocotb
from cocotb.triggers import RisingEdge, Timer
from CocoTBFramework.tbclasses.apb_master.apb_master_tb import APBMasterTB

@cocotb.test()
async def apb_xbar_2to4_test(dut):
    """Test 2-to-4 APB crossbar"""

    # Create testbench
    tb = APBMasterTB(dut)
    await tb.setup_clocks_and_reset()

    # Run tests
    await tb.test_basic_write(addr=0x10000000, data=0xDEADBEEF)
    await tb.test_basic_read(addr=0x10000000)
    # ... more tests

@pytest.mark.parametrize("aw,dw,ba", [
    (32, 32, 0x10000000),
])
def test_apb_xbar_2to4(request, aw, dw, ba):
    """Pytest runner"""
    verilog_sources = [
        "rtl/amba/gaxi/gaxi_fifo_sync.sv",
        "rtl/amba/gaxi/gaxi_skid_buffer.sv",
        "rtl/amba/apb/apb_slave.sv",
        "rtl/amba/apb/apb_master.sv",
        "rtl/common/arbiter_priority_encoder.sv",  # Arbiter dependency
        "rtl/common/arbiter_round_robin.sv",       # Proven arbiter
        "rtl/common/encoder.sv",                   # Address decoding
        "rtl/amba/apb/xbar/apb_xbar_2to4.sv",
        "rtl/integ_amba/apb_xbar/apb_xbar_2to4_wrap.sv",
    ]

    run(
        verilog_sources=verilog_sources,
        toplevel="apb_xbar_2to4_wrap",
        module="test_apb_xbar_2to4",
        parameters={'ADDR_WIDTH': aw, 'DATA_WIDTH': dw, 'BASE_ADDR': ba},
        ...
    )
```

**Step 4: Run Tests**
```bash
cd val/integ_amba
pytest test_apb_xbar_2to4.py -v
```

**Step 5: Integrate into System**

Once tested, integrate into your design:

```systemverilog
module my_soc (
    input  logic        clk,
    input  logic        rst_n,
    // CPU APB master
    // DMA APB master
    // Peripheral slave interfaces
);

    // Instantiate tested crossbar
    apb_xbar_2to4 #(
        .ADDR_WIDTH(32),
        .DATA_WIDTH(32),
        .BASE_ADDR(32'h4000_0000)
    ) u_apb_xbar (
        .pclk       (clk),
        .presetn    (rst_n),
        // Connect to CPU
        .m0_apb_PSEL    (cpu_apb_psel),
        // Connect to DMA
        .m1_apb_PSEL    (dma_apb_psel),
        // Connect to peripherals
        .s0_apb_PSEL    (uart_apb_psel),
        .s1_apb_PSEL    (gpio_apb_psel),
        .s2_apb_PSEL    (timer_apb_psel),
        .s3_apb_PSEL    (spi_apb_psel),
        // ... all other connections
    );

endmodule
```

---

## Advanced Topics

### Extending the Generator

**Add New Features to Generator:**

```python
# In apb_xbar_generator.py

def generate_apb_xbar_with_monitors(num_masters, num_slaves, **kwargs):
    """Generate crossbar with APB monitors on each interface"""

    # Generate base crossbar
    code = generate_apb_xbar(num_masters, num_slaves, **kwargs)

    # Add monitor instantiations
    for m in range(num_masters):
        code += f"""
    // Master {m} APB monitor
    apb_monitor #(
        .ADDR_WIDTH(ADDR_WIDTH),
        .DATA_WIDTH(DATA_WIDTH)
    ) u_apb_mon_m{m} (
        .pclk(pclk), .presetn(presetn),
        .paddr(m{m}_apb_PADDR),
        .psel(m{m}_apb_PSEL),
        .penable(m{m}_apb_PENABLE),
        // ... monitor ports
    );
"""

    return code
```

### Design Space Exploration

**Generate Multiple Configurations:**

```python
# explore_crossbar_configs.py
from apb_xbar_generator import generate_apb_xbar
import os

# Generate MxN matrix of crossbars
for masters in [1, 2, 4, 8]:
    for slaves in [1, 2, 4, 8, 16]:
        filename = f"apb_xbar_{masters}to{slaves}.sv"
        code = generate_apb_xbar(masters, slaves)

        with open(filename, 'w') as f:
            f.write(code)

        # Get statistics
        lines = code.count('\n')
        print(f"{filename}: {lines} lines")
```

### Performance Analysis

**Measure Generated Crossbar Characteristics:**

```bash
# Synthesize and analyze
for xbar in apb_xbar_*.sv; do
    echo "Analyzing $xbar..."
    verilator --lint-only $xbar
    # Add synthesis tool commands here
done
```

### Version Control Integration

**Makefile for Regeneration:**

```makefile
# rtl/amba/apb/xbar/Makefile

GENERATOR = ../../../bin/rtl_generators/amba/apb_xbar_generator.py
SCRIPT = generate_xbars.py

.PHONY: all clean regenerate

all: apb_xbar_1to1.sv apb_xbar_2to1.sv apb_xbar_1to4.sv apb_xbar_2to4.sv

regenerate:
	python $(SCRIPT) --all

apb_xbar_1to1.sv: $(GENERATOR) $(SCRIPT)
	python $(SCRIPT) --masters 1 --slaves 1

apb_xbar_2to1.sv: $(GENERATOR) $(SCRIPT)
	python $(SCRIPT) --masters 2 --slaves 1

apb_xbar_1to4.sv: $(GENERATOR) $(SCRIPT)
	python $(SCRIPT) --masters 1 --slaves 4

apb_xbar_2to4.sv: $(GENERATOR) $(SCRIPT)
	python $(SCRIPT) --masters 2 --slaves 4

clean:
	rm -f apb_xbar_*.sv
```

---

## Troubleshooting

### Common Issues and Solutions

#### Issue 1: Generator Import Error

**Error:**
```
ModuleNotFoundError: No module named 'apb_xbar_generator'
```

**Solution:**
```bash
# Ensure you're in correct directory
cd rtl/amba/apb/xbar

# Or use absolute path
python ../../../bin/rtl_generators/amba/apb_xbar_generator.py
```

#### Issue 2: Verilator Syntax Errors

**Error:**
```
%Error: apb_xbar_2to4.sv:150: syntax error, unexpected '}'
```

**Solution:**
Check for:
- Missing semicolons
- Unbalanced begin/end blocks
- Incorrect for-loop syntax

**Debug:**
```bash
verilator --lint-only apb_xbar_2to4.sv
```

#### Issue 3: Test Failures

**Error:**
```
AssertionError: Expected PRDATA=0xDEADBEEF, got 0x00000000
```

**Solution:**
- Check address map (is address in correct slave range?)
- Verify wrapper port connections
- Check for timing issues (add delays)

**Debug:**
```bash
pytest test_apb_xbar_2to4.py -v -s --vcd=waves.vcd
gtkwave waves.vcd
```

#### Issue 4: Arbitration Not Working

**Symptom:** One master always wins arbitration

**Solution:**
- Check that grant persistence works
- Verify priority rotation logic
- Ensure reset properly initializes arbiters

**Debug Code:**
```systemverilog
// Add to generated crossbar
always @(posedge pclk) begin
    if (s0_grant != '0) begin
        $display("Time %t: Slave 0 grant = %b", $time, s0_grant);
    end
end
```

#### Issue 5: Address Decode Errors

**Symptom:** All accesses return PSLVERR=1

**Solution:**
- Verify BASE_ADDR parameter
- Check address range calculations
- Ensure slave_sel width is correct

**Debug:**
```systemverilog
always @(posedge pclk) begin
    if (m0_cmd_valid) begin
        $display("Master 0: addr=%h, slave_sel=%d, in_range=%b",
                 m0_cmd_paddr, m0_slave_sel, m0_addr_in_range);
    end
end
```

---

## Best Practices

### Generator Best Practices

1. **Version Control Generated Files**
   - Commit generated .sv files to git
   - Include generation date/version in header comments
   - Allows diffing changes when regenerating

2. **Document Generation Commands**
   - Keep README.md with generation instructions
   - Document any customizations made
   - Include example commands

3. **Test After Generation**
   - Always run tests after generating new crossbar
   - Don't assume generator is bug-free
   - Verify critical functionality

4. **Use Meaningful Names**
   - Follow naming convention: `apb_xbar_MtoN.sv`
   - Document purpose in module header
   - Add metadata comments

5. **Validate Parameters**
   - Check ranges (1-16 masters/slaves)
   - Ensure data width is power of 2
   - Verify address alignment

### Integration Best Practices

1. **Start Simple**
   - Begin with 1to1 or 1to4 crossbar
   - Test thoroughly before scaling up
   - Understand architecture before customizing

2. **Isolate for Testing**
   - Create wrapper modules for CocoTB
   - Expose all interfaces as top-level signals
   - Add debug signals if needed

3. **Incremental Integration**
   - Test standalone first
   - Add one master/slave at a time
   - Verify each step before proceeding

4. **Document Address Map**
   - Create clear address map documentation
   - Include in module comments
   - Share with software team

5. **Plan for Debug**
   - Add optional debug signals
   - Consider APB monitors on interfaces
   - Include performance counters

### Code Review Checklist

Before committing generated crossbar:

- [ ] Generator runs without errors
- [ ] No Verilator lint warnings
- [ ] All tests pass
- [ ] Module header comments complete
- [ ] Port naming follows conventions
- [ ] Address map documented
- [ ] Parameters validated
- [ ] README.md updated

---

## Next Steps

### Continue Learning

**Related Tutorials:**
- AXI4 Crossbar Generator (coming soon)
- Custom Protocol Generator (coming soon)
- SystemVerilog Code Generation Patterns

**Advanced Topics:**
- Formal verification of generated code
- Automated test generation
- Performance optimization

### Further Reading

**Internal Documentation:**
- `docs/markdown/RTLAmba/apb/apb_crossbar.md` - Complete crossbar spec
- `rtl/amba/apb/xbar/README.md` - Quick reference
- `bin/rtl_generators/README.md` - Generator framework

**External Resources:**
- ARM IHI0024: AMBA APB Protocol Specification
- Python f-strings documentation
- SystemVerilog LRM IEEE 1800-2017

---

## Appendix: Generator API Reference

### Main Function

```python
def generate_apb_xbar(num_masters, num_slaves, base_addr=0x10000000,
                      addr_width=32, data_width=32, output_file=None)
```

**Parameters:**
- `num_masters` (int): Number of masters (1-16)
- `num_slaves` (int): Number of slaves (1-16)
- `base_addr` (int): Base address for slave 0
- `addr_width` (int): Address bus width (16-64)
- `data_width` (int): Data bus width (8, 16, 32, 64)
- `output_file` (str): Optional output file path

**Returns:**
- `str`: Complete SystemVerilog code

**Raises:**
- `AssertionError`: If parameters out of range

### Helper Functions

```python
def calculate_slave_addr_bits(num_slaves):
    """Calculate address bits needed for slave selection"""
    return max(1, math.ceil(math.log2(num_slaves)))

def generate_module_header(M, N, addr_width, data_width):
    """Generate module declaration and parameters"""

def generate_apb_slave_instance(master_idx, params):
    """Generate single apb_slave instantiation"""

def generate_address_decode(master_idx, num_slaves, base_addr):
    """Generate address decode logic for one master"""

def generate_arbitration(slave_idx, num_masters):
    """Generate round-robin arbitration for one slave"""

def generate_apb_master_instance(slave_idx, params):
    """Generate single apb_master instantiation"""
```

---

## Generating Waveform Diagrams for Documentation

### Using VCD Files from Tests

All crossbar tests generate VCD waveform files that can be converted into documentation-quality timing diagrams:

**Step 1: Run test with VCD generation** (already enabled by default)
```bash
cd val/integ_amba
pytest test_apb_xbar_2to1.py -v
```

**Step 2: Locate VCD file**
```bash
# VCD files are in the sim_build directory
ls local_sim_build/test_apb_xbar_2to1_aw032_dw032/dump.vcd
```

**Step 3: View in GTKWave**
```bash
gtkwave local_sim_build/test_apb_xbar_2to1_aw032_dw032/dump.vcd
```

**Step 4: Create timing diagram**
1. Add signals to GTKWave viewer:
   - `pclk`, `presetn` (clock/reset)
   - `m0_apb_*` (Master 0 signals)
   - `m1_apb_*` (Master 1 signals)
   - `s_apb_*` (Slave signals)
   - Internal arbiter signals (if visible)

2. Zoom to interesting section showing arbitration

3. Export as image:
   - File → Print To File → PNG/PS/PDF

### Recommended Waveform Scenarios

**For 2-to-1 Crossbar (Arbitration):**
- Simultaneous master requests
- Grant rotation after transaction completion
- Grant persistence through PREADY wait states

**For 1-to-4 Crossbar (Address Decode):**
- Single master accessing different slaves
- Address-based routing to 4 different regions
- Slave-specific responses

**For 2-to-4 Crossbar (Full Crossbar):**
- Concurrent master transactions to different slaves
- Arbitration when both masters target same slave
- Independent path operation

### Future: WaveDrom Integration

**Note:** The repository includes infrastructure for automated WaveDrom generation (`bin/CocoTBFramework/tbclasses/wavedrom_user/apb.py`), but crossbar-specific integration is pending. Future enhancement will provide:
- Automated JSON generation from tests
- Protocol-aware signal grouping
- Cycle-accurate timing diagrams
- Direct embedding in markdown documentation

---

## Revision History

| Version | Date | Author | Changes |
|---------|------|--------|---------|
| 1.0 | 2025-10-14 | RTL Design Sherpa | Initial comprehensive tutorial |

---

**Maintained By:** RTL Design Sherpa Project
**Questions/Issues:** See repository issue tracker
**License:** MIT
