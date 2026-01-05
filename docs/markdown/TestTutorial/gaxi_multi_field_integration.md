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

# GAXI Multi-Field Integration Tutorial

**Last Updated:** 2025-10-11
**Difficulty:** Intermediate
**Prerequisites:** Basic SystemVerilog, GAXI protocol fundamentals

---

## Overview

This tutorial demonstrates how to use GAXI (Generic AXI) buffers and FIFOs with structured multi-field data. Instead of treating data as a monolithic bus, you can organize it into multiple semantic fields (address, control, data0, data1, etc.) that maintain their structure through buffering and clock domain crossings.

**Key Concept:** GAXI multi-field wrappers provide a **structured data interface** on top of the generic GAXI infrastructure, making designs more readable and less error-prone.

---

## Why Multi-Field Integration?

### Without Multi-Field (Traditional Approach)

```systemverilog
// ❌ Hard to read, error-prone
wire [31:0] wr_data;  // What does this represent?
assign wr_data = {addr[7:0], ctrl[3:0], data0[11:0], data1[7:0]};

gaxi_skid_buffer #(.DATA_WIDTH(32)) u_buf (
    .wr_data(wr_data),
    .rd_data(rd_data)  // Need to manually unpack!
);

// Manual unpacking - easy to get bit positions wrong!
assign rd_addr  = rd_data[31:24];
assign rd_ctrl  = rd_data[23:20];
assign rd_data0 = rd_data[19:8];
assign rd_data1 = rd_data[7:0];
```

### With Multi-Field (Structured Approach)

```systemverilog
// ✅ Clear, self-documenting
gaxi_skid_buffer_multi #(
    .ADDR_WIDTH(8),
    .CTRL_WIDTH(4),
    .DATA_WIDTH(12)
) u_buf (
    .wr_addr(wr_addr),    // Clear purpose
    .wr_ctrl(wr_ctrl),    // Clear purpose
    .wr_data0(wr_data0),  // Clear purpose
    .wr_data1(wr_data1),  // Clear purpose
    .rd_addr(rd_addr),    // Automatic unpacking
    .rd_ctrl(rd_ctrl),
    .rd_data0(rd_data0),
    .rd_data1(rd_data1)
);
```

**Benefits:**
- **Readability:** Field names document intent
- **Safety:** Compiler checks field widths
- **Maintainability:** Easier to modify field sizes
- **Reusability:** Wrapper pattern scales to any field count

---

## Available Multi-Field Modules

The `rtl/amba/testcode/` directory contains 5 multi-field integration examples:

| Module | Purpose | Clock Domains | Use Case |
|--------|---------|---------------|----------|
| `gaxi_skid_buffer_multi.sv` | 2-stage buffering | Single | Pipeline stages, timing closure |
| `gaxi_skid_buffer_multi_sigmap.sv` | Signal mapping example | Single | Demonstrates custom signal names |
| `gaxi_fifo_sync_multi.sv` | Synchronous FIFO | Single | Packet buffering, rate matching |
| `gaxi_fifo_async_multi.sv` | Asynchronous FIFO | Dual (wr/rd) | Clock domain crossing |
| `gaxi_skid_buffer_async_multi.sv` | Async skid buffer | Dual (wr/rd) | CDC with pipeline stage |

---

## Pattern 1: Synchronous Skid Buffer

### Module: `gaxi_skid_buffer_multi.sv`

**Purpose:** Add 2-stage pipeline buffering to break combinational paths and improve timing.

**Architecture:**
```
Input → Skid Buffer → Output
         (2 stages)
```

**When to Use:**
- Break long combinational paths
- Add buffering for timing closure
- Isolate producer/consumer timing

### Example Integration

```systemverilog
// Transaction structure: address + control + two data fields
gaxi_skid_buffer_multi #(
    .ADDR_WIDTH(16),   // 16-bit address
    .CTRL_WIDTH(8),    // 8-bit control flags
    .DATA_WIDTH(32),   // 32-bit data fields (x2)
    .DEPTH(2)          // 2-stage skid buffer
) u_transaction_buffer (
    .axi_aclk(clk),
    .axi_aresetn(rst_n),

    // Producer side
    .wr_valid(producer_valid),
    .wr_ready(producer_ready),
    .wr_addr(transaction_addr),
    .wr_ctrl(transaction_ctrl),
    .wr_data0(transaction_payload0),
    .wr_data1(transaction_payload1),

    // Consumer side
    .rd_valid(consumer_valid),
    .rd_ready(consumer_ready),
    .rd_addr(buffered_addr),
    .rd_ctrl(buffered_ctrl),
    .rd_data0(buffered_payload0),
    .rd_data1(buffered_payload1)
);
```

**Key Points:**
- **Depth=2:** Two register stages (typical skid buffer)
- **Valid-Ready Handshake:** Standard AXI-style backpressure
- **Zero Bubble:** Can accept new data every cycle when not full
- **Latency:** 2-cycle pipeline delay

---

## Pattern 2: Custom Signal Naming

### Module: `gaxi_skid_buffer_multi_sigmap.sv`

**Purpose:** Demonstrates how to use arbitrary signal names instead of `wr_addr/wr_ctrl/wr_data0/wr_data1`.

**Difference from Pattern 1:**
```systemverilog
// Instead of:  wr_addr, wr_ctrl, wr_data0, wr_data1
// Uses:        wr_siga, wr_sigb, wr_sigc, wr_sigd
// And:         rd_sige, rd_sigf, rd_sigg, rd_sigh
```

**When to Use:**
- Interface with existing code that uses different naming
- Match protocol-specific signal names
- Demonstrate flexibility of wrapper pattern

### Example Integration

```systemverilog
gaxi_skid_buffer_multi_sigmap #(
    .ADDR_WIDTH(12),
    .CTRL_WIDTH(4),
    .DATA_WIDTH(16)
) u_custom_buffer (
    .axi_aclk(clk),
    .axi_aresetn(rst_n),

    // Input with custom names
    .wr_valid(in_valid),
    .wr_ready(in_ready),
    .wr_siga(packet_id),      // Map to addr field
    .wr_sigb(packet_flags),   // Map to ctrl field
    .wr_sigc(packet_header),  // Map to data0 field
    .wr_sigd(packet_footer),  // Map to data1 field

    // Output with custom names
    .rd_valid(out_valid),
    .rd_ready(out_ready),
    .rd_sige(buffered_id),
    .rd_sigf(buffered_flags),
    .rd_sigg(buffered_header),
    .rd_sigh(buffered_footer)
);
```

**Design Pattern:** This shows how to create domain-specific wrappers around generic GAXI infrastructure.

---

## Pattern 3: Synchronous FIFO

### Module: `gaxi_fifo_sync_multi.sv`

**Purpose:** Packet buffering with configurable depth in a single clock domain.

**Architecture:**
```
Input → FIFO (N entries) → Output
        (single clock)
```

**When to Use:**
- Packet queue management
- Rate matching (bursty producer, steady consumer)
- Decouple producer/consumer rates
- Absorb traffic bursts

### Example Integration

```systemverilog
// Command queue: addr + opcode + two 64-bit operands
gaxi_fifo_sync_multi #(
    .ADDR_WIDTH(20),    // 20-bit target address
    .CTRL_WIDTH(8),     // 8-bit opcode
    .DATA_WIDTH(64),    // 64-bit operands (x2)
    .DEPTH(16)          // 16 command slots
) u_command_queue (
    .axi_aclk(sys_clk),
    .axi_aresetn(sys_rst_n),

    // Command producer
    .wr_valid(cmd_issue_valid),
    .wr_ready(cmd_queue_ready),
    .wr_addr(cmd_target_addr),
    .wr_ctrl(cmd_opcode),
    .wr_data0(cmd_operand_a),
    .wr_data1(cmd_operand_b),

    // Command consumer
    .rd_valid(cmd_available),
    .rd_ready(cmd_execute_ready),
    .rd_addr(exec_target_addr),
    .rd_ctrl(exec_opcode),
    .rd_data0(exec_operand_a),
    .rd_data1(exec_operand_b)
);
```

**Depth Sizing Guidelines:**
- **Depth=4-8:** Smooth out minor rate variations
- **Depth=16-32:** Handle bursty traffic patterns
- **Depth=64+:** Large packet buffers, store-and-forward

**FIFO Full/Empty:**
- **wr_ready=0:** FIFO full, producer must stall
- **rd_valid=0:** FIFO empty, consumer must wait

---

## Pattern 4: Asynchronous FIFO (Clock Domain Crossing)

### Module: `gaxi_fifo_async_multi.sv`

**Purpose:** Transfer structured data between two independent clock domains.

**Architecture:**
```
Wr Clock Domain → Async FIFO → Rd Clock Domain
   (wr_clk)      (CDC safe)      (rd_clk)
```

**When to Use:**
- Clock domain crossing (CDC)
- Interface between subsystems with independent clocks
- Frequency ratio conversion
- Asynchronous interfaces

### Example Integration

```systemverilog
// Transfer DMA descriptors from CPU clock to DMA engine clock
gaxi_fifo_async_multi #(
    .ADDR_WIDTH(32),       // 32-bit memory address
    .CTRL_WIDTH(16),       // 16-bit control (length, flags)
    .DATA_WIDTH(32),       // 32-bit metadata (x2)
    .DEPTH(8),             // 8 descriptor slots
    .N_FLOP_CROSS(2),      // 2-flop synchronizer (typical)
    .INSTANCE_NAME("DMA_DESC_FIFO")
) u_dma_descriptor_fifo (
    // CPU clock domain (write side)
    .axi_wr_aclk(cpu_clk),
    .axi_wr_aresetn(cpu_rst_n),
    .wr_valid(desc_issue_valid),
    .wr_ready(desc_fifo_ready),
    .wr_addr(desc_mem_addr),
    .wr_ctrl({desc_length, desc_flags}),
    .wr_data0(desc_src_id),
    .wr_data1(desc_dst_id),

    // DMA engine clock domain (read side)
    .axi_rd_aclk(dma_clk),
    .axi_rd_aresetn(dma_rst_n),
    .rd_valid(desc_available),
    .rd_ready(dma_fetch_ready),
    .rd_addr(dma_mem_addr),
    .rd_ctrl({dma_length, dma_flags}),
    .rd_data0(dma_src_id),
    .rd_data1(dma_dst_id)
);
```

**Critical CDC Parameters:**
- **N_FLOP_CROSS=2:** Typical for most designs (reduces MTBF)
- **N_FLOP_CROSS=3:** Use for very high-speed or critical paths
- **DEPTH:** Must be power of 2 for Gray code pointers
- **INSTANCE_NAME:** Helps identify FIFO in timing reports

**CDC Safety:**
- Uses Gray code for pointer crossing
- Multi-stage synchronizers (configurable)
- Handles arbitrary clock frequency ratios
- Safe for reset desynchronization

---

## Pattern 5: Async Skid Buffer (CDC + Pipeline)

### Module: `gaxi_skid_buffer_async_multi.sv`

**Purpose:** Combines async FIFO with input-side skid buffer for optimal CDC performance.

**Architecture:**
```
Wr Clock → Skid Buffer → Async FIFO → Rd Clock
  (wr_clk)   (2 stages)   (CDC safe)   (rd_clk)
```

**When to Use:**
- CDC with guaranteed zero-bubble acceptance on write side
- High-performance clock domain crossing
- When producer can't tolerate long ready latency
- Isolate CDC latency from producer timing

### Example Integration

```systemverilog
// High-performance packet crossing with input buffering
gaxi_skid_buffer_async_multi #(
    .ADDR_WIDTH(16),
    .CTRL_WIDTH(8),
    .DATA_WIDTH(64),
    .DEPTH(16),           // Async FIFO depth
    .N_FLOP_CROSS(2),
    .INSTANCE_NAME("PKT_CDC")
) u_packet_cdc (
    // Fast clock domain (write)
    .axi_wr_aclk(fast_clk),      // e.g., 500MHz
    .axi_wr_aresetn(fast_rst_n),
    .wr_valid(fast_pkt_valid),
    .wr_ready(fast_pkt_ready),   // Low latency (skid buffer)
    .wr_addr(fast_pkt_id),
    .wr_ctrl(fast_pkt_type),
    .wr_data0(fast_pkt_data_lo),
    .wr_data1(fast_pkt_data_hi),

    // Slow clock domain (read)
    .axi_rd_aclk(slow_clk),      // e.g., 100MHz
    .axi_rd_aresetn(slow_rst_n),
    .rd_valid(slow_pkt_valid),
    .rd_ready(slow_pkt_ready),
    .rd_addr(slow_pkt_id),
    .rd_ctrl(slow_pkt_type),
    .rd_data0(slow_pkt_data_lo),
    .rd_data1(slow_pkt_data_hi)
);
```

**Performance Benefits:**
- **Low Write Latency:** Skid buffer absorbs immediate backpressure
- **CDC Isolation:** Async FIFO handles clock crossing
- **High Throughput:** Can accept bursts without stalls

**Trade-offs:**
- **More Resources:** Combines two storage elements
- **Higher Latency:** Additional pipeline stages
- **Best for:** High-speed producers that can't tolerate CDC latency

---

## Creating Custom Multi-Field Wrappers

### Step 1: Define Your Fields

```systemverilog
// Example: Network packet with 3 fields
parameter int PACKET_ID_WIDTH   = 12;  // Packet identifier
parameter int PACKET_TYPE_WIDTH = 4;   // Type/opcode
parameter int PAYLOAD_WIDTH     = 128; // Payload data
```

### Step 2: Calculate Total Width

```systemverilog
localparam int TOTAL_WIDTH = PACKET_ID_WIDTH + PACKET_TYPE_WIDTH + PAYLOAD_WIDTH;
// = 12 + 4 + 128 = 144 bits
```

### Step 3: Create Wrapper Module

```systemverilog
module network_packet_buffer #(
    parameter int DEPTH = 16
) (
    input  logic axi_aclk,
    input  logic axi_aresetn,

    // Input packet
    input  logic                           wr_valid,
    output logic                           wr_ready,
    input  logic [PACKET_ID_WIDTH-1:0]    wr_packet_id,
    input  logic [PACKET_TYPE_WIDTH-1:0]  wr_packet_type,
    input  logic [PAYLOAD_WIDTH-1:0]      wr_payload,

    // Output packet
    output logic                           rd_valid,
    input  logic                           rd_ready,
    output logic [PACKET_ID_WIDTH-1:0]    rd_packet_id,
    output logic [PACKET_TYPE_WIDTH-1:0]  rd_packet_type,
    output logic [PAYLOAD_WIDTH-1:0]      rd_payload
);

    // Instantiate generic GAXI FIFO
    gaxi_fifo_sync #(
        .DATA_WIDTH(TOTAL_WIDTH),
        .DEPTH(DEPTH)
    ) u_fifo (
        .axi_aclk(axi_aclk),
        .axi_aresetn(axi_aresetn),

        // Pack fields on write
        .wr_valid(wr_valid),
        .wr_ready(wr_ready),
        .wr_data({wr_packet_id, wr_packet_type, wr_payload}),

        // Unpack fields on read
        .rd_valid(rd_valid),
        .rd_ready(rd_ready),
        .rd_data({rd_packet_id, rd_packet_type, rd_payload}),

        .count()  // Optional: monitor FIFO occupancy
    );

endmodule
```

### Step 4: Use Your Custom Wrapper

```systemverilog
network_packet_buffer #(.DEPTH(32)) u_rx_queue (
    .axi_aclk(rx_clk),
    .axi_aresetn(rx_rst_n),
    .wr_valid(rx_packet_valid),
    .wr_ready(rx_queue_ready),
    .wr_packet_id(rx_id),
    .wr_packet_type(rx_type),
    .wr_payload(rx_data),
    .rd_valid(process_packet_valid),
    .rd_ready(process_packet_ready),
    .rd_packet_id(process_id),
    .rd_packet_type(process_type),
    .rd_payload(process_data)
);
```

---

## Field Packing Strategies

### Strategy 1: Concatenation Order Matters

```systemverilog
// ❌ WRONG: Inconsistent packing/unpacking
.wr_data({wr_addr, wr_ctrl, wr_data1, wr_data0})  // data1 before data0
.rd_data({rd_addr, rd_ctrl, rd_data0, rd_data1})  // data0 before data1 - MISMATCH!
```

```systemverilog
// ✅ CORRECT: Consistent ordering
.wr_data({wr_addr, wr_ctrl, wr_data1, wr_data0})
.rd_data({rd_addr, rd_ctrl, rd_data1, rd_data0})
```

**Rule:** Always use the same concatenation order for write and read!

### Strategy 2: MSB-to-LSB Convention

```systemverilog
// Recommended: MSB to LSB (left to right)
{highest_priority_field, ..., lowest_priority_field}

// Example:
{addr[15:0], ctrl[7:0], data1[31:0], data0[31:0]}
//  ^MSB                                        ^LSB
```

### Strategy 3: Document Field Positions

```systemverilog
// Total width: 88 bits
// [87:72] - addr  (16 bits)
// [71:64] - ctrl  (8 bits)
// [63:32] - data1 (32 bits)
// [31:0]  - data0 (32 bits)
wire [87:0] packed_data = {addr, ctrl, data1, data0};
```

---

## Testing Multi-Field Modules

### Test Infrastructure

All multi-field modules have comprehensive tests in `val/integ_amba/`:

- `test_gaxi_buffer_multi.py` - Tests skid buffers and sync FIFOs
- `test_gaxi_buffer_multi_sigmap.py` - Tests signal mapping variant

### Example Test Pattern

```python
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_multi import GaxiMultiBufferTB

@cocotb.test()
async def test_multi_field_buffer(dut):
    tb = GaxiMultiBufferTB(dut, wr_clk=dut.axi_aclk, wr_rstn=dut.axi_aresetn)

    # Run comprehensive tests
    result = await tb.run_sequence_test(
        tb.comprehensive_sequence,
        delay_key='constrained',
        delay_clks_after=10
    )

    assert result, "Multi-field test failed verification"
```

### Key Test Scenarios

1. **Basic Sequence:** Simple incremental patterns
2. **Walking Ones:** Detect stuck-at faults in each field
3. **Alternating Patterns:** Toggle all bits
4. **Burst Sequence:** Back-to-back transactions
5. **Random Data:** Coverage of value space
6. **Slow Producer:** Test backpressure from input
7. **Slow Consumer:** Test backpressure from output
8. **Stress Test:** Combined burst and pause patterns

---

## Design Guidelines

### 1. Field Width Selection

```systemverilog
// ✅ GOOD: Power-of-2 or natural widths
parameter ADDR_WIDTH = 16;  // 2^16 addresses
parameter CTRL_WIDTH = 8;   // Byte-aligned
parameter DATA_WIDTH = 32;  // Word-aligned

// ⚠️ ACCEPTABLE: Non-power-of-2 when needed
parameter TAG_WIDTH  = 12;  // 4096 tags (actual requirement)
```

### 2. Depth Selection

```systemverilog
// Skid buffers: Always DEPTH=2
gaxi_skid_buffer_multi #(.DEPTH(2)) ...

// Sync FIFOs: Power-of-2 recommended but not required
gaxi_fifo_sync_multi #(.DEPTH(16)) ...   // ✅ Power-of-2
gaxi_fifo_sync_multi #(.DEPTH(20)) ...   // ⚠️ Works but less efficient

// Async FIFOs: MUST be power-of-2 (Gray code requirement)
gaxi_fifo_async_multi #(.DEPTH(16)) ...  // ✅ Required
gaxi_fifo_async_multi #(.DEPTH(20)) ...  // ❌ Will not work!
```

### 3. Reset Strategy

```systemverilog
// All modules use active-low async reset
input logic axi_aresetn  // ✅ Standard convention

// For dual-clock modules
input logic axi_wr_aresetn,  // Independent resets
input logic axi_rd_aresetn   // Can reset domains separately
```

### 4. Naming Conventions

```systemverilog
// ✅ GOOD: Descriptive field names
.wr_transaction_id(...)
.wr_opcode(...)
.wr_operand_a(...)

// ❌ BAD: Generic names lose information
.wr_data0(...)
.wr_data1(...)
.wr_data2(...)
```

---

## Common Pitfalls

### Pitfall 1: Mismatched Field Widths

```systemverilog
// ❌ WRONG
gaxi_skid_buffer_multi #(
    .ADDR_WIDTH(16),
    .CTRL_WIDTH(8),
    .DATA_WIDTH(32)
) u_buf (
    .wr_addr(addr[11:0]),   // ❌ Only 12 bits, but parameter says 16!
    ...
);
```

**Fix:** Match signal widths to parameters or use explicit truncation/extension.

### Pitfall 2: Forgetting Valid-Ready Protocol

```systemverilog
// ❌ WRONG: Ignoring ready signal
always_ff @(posedge clk) begin
    wr_valid <= 1'b1;
    wr_data  <= new_data;  // Could be lost if wr_ready=0!
end
```

```systemverilog
// ✅ CORRECT: Check ready before asserting valid
always_ff @(posedge clk) begin
    if (wr_ready || !wr_valid) begin
        wr_valid <= has_data;
        wr_data  <= new_data;
    end
end
```

### Pitfall 3: Async FIFO Non-Power-of-2 Depth

```systemverilog
// ❌ WRONG: Async FIFO requires power-of-2
gaxi_fifo_async_multi #(.DEPTH(20)) ...  // Simulation may pass, synthesis fails!
```

**Fix:** Always use power-of-2 depths for async FIFOs.

---

## Performance Considerations

### Latency

| Module | Write Latency | Read Latency | Total |
|--------|--------------|--------------|-------|
| Skid Buffer (sync) | 2 cycles | 0 cycles | 2 cycles |
| FIFO (sync) | 1 cycle | 1 cycle | 2 cycles |
| FIFO (async) | 3-4 cycles | 3-4 cycles | 6-8 cycles |
| Skid+Async | 2 + (3-4) | 3-4 cycles | 8-10 cycles |

### Throughput

- **Skid Buffer:** 1 transaction/cycle (zero bubble)
- **FIFO (sync):** 1 transaction/cycle (when not full/empty)
- **FIFO (async):** Limited by slower clock domain

### Resource Usage

**Per Entry (approximate):**
- Skid buffer: ~2x data width in FFs
- Sync FIFO: ~1x data width in FFs or BRAM
- Async FIFO: ~1x data width + Gray code overhead

---

## Summary

**Multi-field GAXI wrappers provide:**
1. ✅ **Structured data interfaces** - Self-documenting field names
2. ✅ **Type safety** - Compiler-checked field widths
3. ✅ **Reusability** - Pattern scales to any protocol
4. ✅ **Maintainability** - Easy to modify field structure
5. ✅ **Testability** - Field-level observability

**When to use each module:**
- **Skid buffer:** Timing closure, pipeline stages
- **Sync FIFO:** Packet buffering, rate matching
- **Async FIFO:** Clock domain crossing
- **Async skid:** High-performance CDC

**Next Steps:**
- See [GAXI Field Configuration Guide](gaxi_field_configuration.md) for advanced patterns
- Review tests in `val/integ_amba/test_gaxi_buffer_multi.py`
- Explore testcode modules in `rtl/amba/testcode/`

---

**Related Documentation:**
- [GAXI Protocol Overview](../RTLAmba/fabric/gaxi_overview.md)
- [Clock Domain Crossing Best Practices](../RTLCommon/cdc_guidelines.md)
- [Advanced Test Examples](advanced_examples.md)
