# GAXI Register Slice

**Module:** `gaxi_regslice.sv`
**Location:** `rtl/amba/gaxi/`
**Status:** ✅ Production Ready

---

## Overview

The GAXI register slice provides a timing-friendly 1-deep elastic buffer for pipeline timing isolation. It implements the classic register slice pattern with always-registered data transfer, guaranteeing predictable 1-cycle latency and consistent throughput.

### Key Features

- ✅ **Fixed 1-Cycle Latency:** Always registered, predictable timing
- ✅ **Full Throughput:** 1 beat/cycle in steady state
- ✅ **Elastic Buffering:** Absorbs single-cycle backpressure
- ✅ **Port Compatible:** Intentionally aligned with gaxi_skid_buffer
- ✅ **Ready/Valid Handshake:** Industry-standard AXI-like protocol
- ✅ **Minimal Resources:** Single register stage

---

## Module Interface

```systemverilog
module gaxi_regslice #(
    parameter int DATA_WIDTH   = 32,
    parameter     INSTANCE_NAME = "REGSL1D",
    parameter int DW           = DATA_WIDTH    // Derived
) (
    // Global Clock and Reset
    input  logic          axi_aclk,
    input  logic          axi_aresetn,

    // Write Interface (Input Side)
    input  logic          wr_valid,
    output logic          wr_ready,
    input  logic [DW-1:0] wr_data,

    // Read Interface (Output Side)
    output logic          rd_valid,
    input  logic          rd_ready,
    output logic [DW-1:0] rd_data,

    // Status/Monitoring
    output logic [3:0]    count,      // 0 or 1
    output logic [3:0]    rd_count    // mirror of count
);
```

---

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `DATA_WIDTH` | 32 | Data bus width (arbitrary) |
| `INSTANCE_NAME` | "REGSL1D" | Debug instance name |
| `DW` | DATA_WIDTH | Derived parameter (internal use) |

---

## Functional Description

### Architecture

The register slice implements a single-entry elastic buffer with simultaneous push/pop capability:

```
                   ┌─────────────────────┐
    wr_valid ─────>│                     │
    wr_ready <─────│  1-Entry Storage    │
    wr_data  ─────>│  - r_valid (1-bit)  │
                   │  - r_data  (DW-bit) │
                   │                     │────> rd_data (registered)
                   │  Handshake Logic    │
                   │  - Accept when      │
    rd_ready ─────>│    empty OR pop     │
    rd_valid <─────│                     │
    count    <─────│  Status: 0 or 1     │
                   └─────────────────────┘
```

### Ready/Valid Protocol

**Write Ready Conditions:**
```systemverilog
wr_ready = (!r_valid) || (r_valid && rd_ready)
```
- Accept when storage is **empty** (r_valid=0)
- Accept when storage is **full** AND downstream **consuming** (simultaneous transfer)

**Read Valid:**
```systemverilog
rd_valid = r_valid
```
- Valid when storage is occupied

### Transfer Scenarios

| Scenario | wr_valid | wr_ready | rd_valid | rd_ready | Action |
|----------|----------|----------|----------|----------|--------|
| **Idle** | 0 | 1 (empty) | 0 | X | Storage empty, ready to accept |
| **Fill** | 1 | 1 | 0 | X | Write data → storage, r_valid=1 |
| **Full** | 0 | 0 | 1 | 0 | Storage occupied, downstream not consuming |
| **Drain** | 0 | 1 (will empty) | 1 | 1 | Read consumes data, r_valid=0 |
| **Pass-through** | 1 | 1 | 1 | 1 | Simultaneous write+read, data passes through |

### Storage Update Logic

```systemverilog
unique case ({w_wxfer, w_rxfer})
    2'b10: begin  // Write only: fill
        r_valid <= 1'b1;
        r_data  <= wr_data;
    end
    2'b01: begin  // Read only: drain
        r_valid <= 1'b0;
    end
    2'b11: begin  // Simultaneous: pass through with register
        r_valid <= 1'b1;
        r_data  <= wr_data;
    end
    default: begin  // Idle: hold state
        r_valid <= r_valid;
        r_data  <= r_data;
    end
endcase
```

---

## Usage Examples

### Example 1: Pipeline Timing Isolation

```systemverilog
// Insert register slice to break long combinatorial path
gaxi_regslice #(
    .DATA_WIDTH(64)
) u_pipeline_break (
    .axi_aclk     (clk),
    .axi_aresetn  (rst_n),
    .wr_valid     (stage1_valid),
    .wr_ready     (stage1_ready),
    .wr_data      (stage1_data),
    .rd_valid     (stage2_valid),
    .rd_ready     (stage2_ready),
    .rd_data      (stage2_data),
    .count        ()  // Optional monitoring
);
```

### Example 2: AXI Channel Register Slice

```systemverilog
// Register slice for AXI AR channel
gaxi_regslice #(
    .DATA_WIDTH(AXI_ID_WIDTH + AXI_ADDR_WIDTH + 8 + 3 + 2),
    .INSTANCE_NAME("AR_REGSL")
) u_ar_regslice (
    .axi_aclk     (aclk),
    .axi_aresetn  (aresetn),
    .wr_valid     (m_axi_arvalid),
    .wr_ready     (m_axi_arready),
    .wr_data      ({m_axi_arid, m_axi_araddr, m_axi_arlen,
                    m_axi_arsize, m_axi_arburst}),
    .rd_valid     (s_axi_arvalid),
    .rd_ready     (s_axi_arready),
    .rd_data      ({s_axi_arid, s_axi_araddr, s_axi_arlen,
                    s_axi_arsize, s_axi_arburst}),
    .count        (ar_occupancy)
);
```

### Example 3: Multiple Register Slices for Deep Pipelining

```systemverilog
// Chain multiple register slices for multi-cycle pipeline
gaxi_regslice #(.DATA_WIDTH(32)) u_stage1 (
    .axi_aclk(clk), .axi_aresetn(rst_n),
    .wr_valid(in_valid),   .wr_ready(in_ready),   .wr_data(in_data),
    .rd_valid(pipe1_valid), .rd_ready(pipe1_ready), .rd_data(pipe1_data)
);

gaxi_regslice #(.DATA_WIDTH(32)) u_stage2 (
    .axi_aclk(clk), .axi_aresetn(rst_n),
    .wr_valid(pipe1_valid), .wr_ready(pipe1_ready), .wr_data(pipe1_data),
    .rd_valid(pipe2_valid), .rd_ready(pipe2_ready), .rd_data(pipe2_data)
);

gaxi_regslice #(.DATA_WIDTH(32)) u_stage3 (
    .axi_aclk(clk), .axi_aresetn(rst_n),
    .wr_valid(pipe2_valid), .wr_ready(pipe2_ready), .wr_data(pipe2_data),
    .rd_valid(out_valid), .rd_ready(out_ready), .rd_data(out_data)
);
// Total latency: 3 cycles, full throughput maintained
```

---

## Timing Characteristics

| Characteristic | Value | Notes |
|---------------|-------|-------|
| Write→Read Latency | **1 cycle** | Always registered, fixed latency |
| Max Throughput | **1 beat/cycle** | Sustained in steady state |
| Backpressure Absorption | **1 beat** | Single-entry elastic buffer |
| Read Path | **Registered** | No combinatorial paths |
| Write Path | **Combinatorial** | wr_ready depends on rd_ready |

### Latency Guarantee

Unlike skid buffers which can have 0-cycle bypass, the register slice **always** introduces 1-cycle latency:

```
Cycle:   1      2      3      4      5
         ─────  ─────  ─────  ─────  ─────
wr_valid   ╱‾‾╲_____________________
wr_data  =[ A ]=====================

r_valid  ________╱‾‾‾‾‾‾‾‾‾╲_________
r_data   ========[ A ]================

rd_valid ________╱‾‾‾‾‾‾‾‾‾╲_________
rd_data  ========[ A ]================
         ↑
         1-cycle delay guaranteed
```

---

## Comparison with Related Modules

### gaxi_regslice vs gaxi_skid_buffer

| Feature | gaxi_regslice | gaxi_skid_buffer |
|---------|---------------|------------------|
| **Depth** | 1 entry | 1 entry (+ skid slot) |
| **Latency** | **1 cycle (fixed)** | 0-1 cycle (variable) |
| **Bypass Path** | ❌ No | ✅ Yes (when empty) |
| **Throughput** | 1 beat/cycle | 1 beat/cycle |
| **Use Case** | **Timing isolation** | **Low latency** |
| **Registered Output** | ✅ Always | ⚠️ Only when filled |
| **Timing Closure** | ✅ Better (no bypass) | ⚠️ Has combinatorial bypass |

**When to Choose:**
- **gaxi_regslice:** Timing closure priority, need predictable latency
- **gaxi_skid_buffer:** Latency-sensitive paths, tolerate variable timing

### gaxi_regslice vs gaxi_fifo_sync

| Feature | gaxi_regslice | gaxi_fifo_sync |
|---------|---------------|----------------|
| **Depth** | 1 entry (fixed) | Parameterized (N entries) |
| **Latency** | 1 cycle | 1-2 cycles (mode-dependent) |
| **Resources** | Minimal (1 register) | Scales with depth |
| **Use Case** | Pipeline breaks | Buffering, rate matching |

---

## Resource Utilization

### FPGA Resources (Typical)

| DATA_WIDTH | Flops | LUTs | Slice Registers |
|------------|-------|------|-----------------|
| 8 | 9 | ~6 | 9 |
| 32 | 33 | ~12 | 33 |
| 64 | 65 | ~18 | 65 |
| 128 | 129 | ~24 | 129 |

**Scaling:** Approximately DATA_WIDTH + 1 flops (data + valid flag)

---

## Testing

### Test Coverage

**Test File:** `val/amba/test_gaxi_regslice.py`

**Test Methods:**
- Simple incremental loops (fill/drain cycles)
- Back-to-back transfers (sustained throughput)
- Comprehensive randomizer sweep (varied timing patterns)
- Stress test with random patterns

**Test Levels:**
- **basic:** Quick smoke test (~30s, 4 loops)
- **medium:** Moderate coverage (~2min, expanded patterns)
- **full:** Comprehensive validation (~5min, 100+ loops)

### Run Tests

```bash
# Basic test (quick validation)
TEST_LEVEL=basic pytest val/amba/test_gaxi_regslice.py -v

# Medium test (normal CI)
TEST_LEVEL=medium pytest val/amba/test_gaxi_regslice.py -v

# Full test (pre-release validation)
TEST_LEVEL=full pytest val/amba/test_gaxi_regslice.py -v
```

---

## Design Considerations

### Port Compatibility

**Intentional alignment with gaxi_skid_buffer allows drop-in replacement:**

```systemverilog
// Both modules share identical port signatures
gaxi_regslice #(.DATA_WIDTH(64)) u_option1 (...);
gaxi_skid_buffer #(.DATA_WIDTH(64)) u_option2 (...);
```

This enables easy experimentation:
- Start with **gaxi_skid_buffer** for low latency
- Upgrade to **gaxi_regslice** if timing closure issues arise

### Status Signals

**count and rd_count are 4-bit for interface compatibility:**
- Value 0: Storage empty
- Value 1: Storage occupied
- Both signals always equal (redundant, but matches skid buffer interface)

### Assertions

Built-in simulation checks (disabled in synthesis):
```systemverilog
// Detect backpressure hot spots
if (wr_valid && !wr_ready) ...

// Detect invalid reads
if (rd_ready && !rd_valid) ...

// Sanity check
if (count > 4'd1) $error(...)
```

---

## Related Modules

- [gaxi_skid_buffer](gaxi_skid_buffer.md) - Zero-latency bypass alternative
- [gaxi_fifo_sync](gaxi_fifo_sync.md) - Multi-entry FIFO version
- [gaxi_fifo_async](gaxi_fifo_async.md) - Clock domain crossing version
- [GAXI Index](index.md) - Overview of all GAXI modules

---

## Common Use Cases

### 1. Breaking Long Combinatorial Paths

Problem: Critical path through multiple modules
```systemverilog
// Before: Long combinatorial path
assign module_b_in = complex_function(module_a_out);
```

Solution: Insert register slice
```systemverilog
// After: Broken with 1-cycle register
gaxi_regslice #(.DATA_WIDTH(32)) u_break (
    .axi_aclk(clk), .axi_aresetn(rst_n),
    .wr_valid(module_a_valid), .wr_data(module_a_out), .wr_ready(module_a_ready),
    .rd_valid(module_b_valid), .rd_data(module_b_in),   .rd_ready(module_b_ready)
);
```

### 2. AXI Interface Pipelining

Improve timing across AXI channels:
```systemverilog
// Pipeline all 5 AXI4 channels
gaxi_regslice #(...) u_ar_slice (...);  // Address Read
gaxi_regslice #(...) u_r_slice  (...);  // Read Data
gaxi_regslice #(...) u_aw_slice (...);  // Address Write
gaxi_regslice #(...) u_w_slice  (...);  // Write Data
gaxi_regslice #(...) u_b_slice  (...);  // Write Response
```

### 3. CDC Preparation

Use before async FIFO to ensure registered inputs:
```systemverilog
// Register slice before CDC FIFO
gaxi_regslice #(.DATA_WIDTH(32)) u_pre_cdc (
    .axi_aclk(clk_a), .axi_aresetn(rst_a_n),
    .wr_valid(src_valid), .wr_data(src_data), .wr_ready(src_ready),
    .rd_valid(fifo_wr_valid), .rd_data(fifo_wr_data), .rd_ready(fifo_wr_ready)
);

gaxi_fifo_async #(.DATA_WIDTH(32), .DEPTH(16)) u_cdc_fifo (
    .wr_clk(clk_a), .rd_clk(clk_b), ...
    .wr_valid(fifo_wr_valid), .wr_data(fifo_wr_data), .wr_ready(fifo_wr_ready),
    ...
);
```

---

**Version:** 1.0
**Last Updated:** 2025-10-23
