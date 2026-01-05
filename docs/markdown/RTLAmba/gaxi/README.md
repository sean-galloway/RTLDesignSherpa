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

# GAXI (Generic AXI) Modules

**Location:** `rtl/amba/gaxi/`
**Test Location:** `val/amba/`
**Status:** ✅ Production Ready

---

## Overview

The GAXI subsystem provides a lightweight valid/ready handshake protocol for streaming data between components. Simpler than full AXI4-Stream while maintaining robust flow control, GAXI is used throughout the RTL Design Sherpa infrastructure for elastic buffering, clock domain crossing, and timing closure.

### Key Features

- ✅ **Simple Handshake:** Valid/ready only - minimal overhead
- ✅ **Elastic Buffering:** Skid buffers for zero-latency bypass
- ✅ **Clock Domain Crossing:** Async variants with proper CDC
- ✅ **Type-Safe Structs:** Struct-aware buffers for complex data
- ✅ **Drop Capability:** Special FIFO variant with drop-by-count/drop-all
- ✅ **Flexible Modes:** Mux/flop output modes for area/speed trade-offs

---

## Module Categories

### Skid Buffers (Elastic Buffering)

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **gaxi_skid_buffer** | Synchronous elastic buffer with zero-latency bypass | [gaxi_skid_buffer.md](gaxi_skid_buffer.md) | ✅ Documented |
| **gaxi_skid_buffer_struct** | Type-parameterized variant for complex structs | [gaxi_skid_buffer_struct.md](gaxi_skid_buffer_struct.md) | ✅ Documented |
| **gaxi_skid_buffer_async** | Asynchronous elastic buffer for CDC | [gaxi_skid_buffer_async.md](gaxi_skid_buffer_async.md) | ✅ Documented |

### FIFOs (Deep Buffering)

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **gaxi_fifo_sync** | Synchronous FIFO with mux/flop modes | [gaxi_fifo_sync.md](gaxi_fifo_sync.md) | ✅ Documented |
| **gaxi_fifo_async** | Asynchronous FIFO for clock domain crossing | [gaxi_fifo_async.md](gaxi_fifo_async.md) | ✅ Documented |
| **gaxi_drop_fifo_sync** | FIFO with drop-by-count and drop-all capability | [gaxi_drop_fifo_sync.md](gaxi_drop_fifo_sync.md) | ✅ Documented |

---

## Protocol Overview

### Interface Signals

**Write Interface (Producer):**
- `wr_valid` - Data valid from source
- `wr_ready` - Ready to accept data (backpressure)
- `wr_data[N:0]` - Data from source

**Read Interface (Consumer):**
- `rd_valid` - Data valid to sink
- `rd_ready` - Ready to accept data from sink
- `rd_data[N:0]` - Data to sink

**Optional Monitoring:**
- `count[3:0]` - Current FIFO/buffer occupancy

### Handshake Rules

1. **Transfer:** Occurs when `valid && ready` on rising clock edge
2. **Data Stability:** `data` must be stable when `valid` is high
3. **Backpressure:** `ready` may deassert to apply backpressure
4. **Valid Persistence:** `valid` must remain high until transfer completes

---

## Quick Start

### Basic Skid Buffer (Zero-Latency)

```systemverilog
gaxi_skid_buffer #(
    .DATA_WIDTH(32),
    .DEPTH(4)           // 4 entries
) u_skid (
    .axi_aclk    (clk),
    .axi_aresetn (rst_n),

    // Write port (from producer)
    .wr_valid    (src_valid),
    .wr_ready    (src_ready),
    .wr_data     (src_data),

    // Read port (to consumer)
    .rd_valid    (dst_valid),
    .rd_ready    (dst_ready),
    .rd_data     (dst_data),

    // Status
    .count       (buf_count),
    .rd_count    ()
);
```

### Synchronous FIFO (Deep Buffering)

```systemverilog
gaxi_fifo_sync #(
    .DATA_WIDTH(64),
    .DEPTH(64),         // 64 entries
    .REGISTERED(0)      // 0=mux mode (fast), 1=flop mode (more area)
) u_fifo (
    .axi_aclk    (clk),
    .axi_aresetn (rst_n),

    .wr_valid    (wr_valid),
    .wr_ready    (wr_ready),
    .wr_data     (wr_data),

    .rd_valid    (rd_valid),
    .rd_ready    (rd_ready),
    .rd_data     (rd_data),

    .count       (fifo_level)
);
```

### Asynchronous FIFO (Clock Domain Crossing)

```systemverilog
gaxi_fifo_async #(
    .DATA_WIDTH(32),
    .DEPTH(16),         // Must be power of 2
    .N_FLOP_CROSS(3),   // CDC synchronizer stages
    .REGISTERED(0)
) u_async_fifo (
    // Write domain
    .axi_wr_aclk    (wr_clk),
    .axi_wr_aresetn (wr_rst_n),
    .wr_valid       (wr_valid),
    .wr_ready       (wr_ready),
    .wr_data        (wr_data),

    // Read domain
    .axi_rd_aclk    (rd_clk),
    .axi_rd_aresetn (rd_rst_n),
    .rd_valid       (rd_valid),
    .rd_ready       (rd_ready),
    .rd_data        (rd_data)
);
```

### Type-Safe Struct Buffer

```systemverilog
// Define AXI AR channel struct
typedef struct packed {
    logic [7:0]  arid;
    logic [31:0] araddr;
    logic [7:0]  arlen;
    logic [2:0]  arsize;
    logic [1:0]  arburst;
} axi_ar_t;

// Struct-aware buffer
gaxi_skid_buffer_struct #(
    .STRUCT_TYPE(axi_ar_t),
    .DEPTH(4)
) u_ar_buf (
    .axi_aclk    (clk),
    .axi_aresetn (rst_n),

    .wr_valid    (master_arvalid),
    .wr_ready    (master_arready),
    .wr_data     (master_ar),      // Type-safe struct

    .rd_valid    (slave_arvalid),
    .rd_ready    (slave_arready),
    .rd_data     (slave_ar),       // Type-safe struct

    .count       (ar_count)
);
```

### Drop FIFO (Packet Processing)

```systemverilog
gaxi_drop_fifo_sync #(
    .DATA_WIDTH(512),
    .DEPTH(64),
    .REGISTERED(1)      // Flop mode for 512-bit width
) u_drop_fifo (
    .axi_aclk        (clk),
    .axi_aresetn     (rst_n),

    .wr_valid        (pkt_valid),
    .wr_ready        (pkt_ready),
    .wr_data         (pkt_data),

    .rd_valid        (proc_valid),
    .rd_ready        (proc_ready),
    .rd_data         (proc_data),

    // Drop control
    .drop_count      (drop_n_packets),  // Drop N oldest entries
    .drop_count_valid(drop_trigger),
    .drop_all        (flush_fifo),      // Flush entire FIFO

    .count           (pkt_count)
);
```

---

## Testing

All GAXI modules are verified using CocoTB-based testbenches:

```bash
# Run all GAXI tests
pytest val/amba/test_gaxi*.py -v

# Run specific module tests
pytest val/amba/test_gaxi_buffer_sync.py -v      # Skid buffers + sync FIFOs
pytest val/amba/test_gaxi_buffer_async.py -v     # Async FIFO
pytest val/amba/test_gaxi_drop_fifo_sync.py -v   # Drop FIFO

# Run with waveforms
pytest val/amba/test_gaxi_buffer_sync.py --vcd=waves.vcd -v

# Generate WaveDrom timing diagrams
pytest val/amba/test_gaxi_wavedrom_example.py -v
cd val/amba && bash wd_cmd.sh  # Generate PNG/SVG
```

---

## Design Patterns

### Pattern 1: Timing Closure (Pipeline Stage)

Use skid buffer to break combinatorial paths:

```systemverilog
// Without buffer: long combinatorial path
assign downstream_data = upstream_data;  // May not meet timing

// With skid buffer: registered boundary
gaxi_skid_buffer #(.DATA_WIDTH(32), .DEPTH(2)) u_pipeline (
    .wr_valid(upstream_valid),
    .wr_ready(upstream_ready),
    .wr_data(upstream_data),
    .rd_valid(downstream_valid),
    .rd_ready(downstream_ready),
    .rd_data(downstream_data),
    ...
);
```

### Pattern 2: Rate Adaptation

Use FIFO to handle burst traffic:

```systemverilog
// Bursty writer, continuous reader
gaxi_fifo_sync #(.DATA_WIDTH(64), .DEPTH(64)) u_rate_adapter (
    .wr_valid(bursty_valid),     // Intermittent bursts
    .wr_ready(bursty_ready),
    .wr_data(bursty_data),
    .rd_valid(continuous_valid),  // Always reading
    .rd_ready(continuous_ready),
    .rd_data(continuous_data),
    ...
);
```

### Pattern 3: Clock Domain Crossing

Use async FIFO for safe CDC:

```systemverilog
// Domain A → Domain B
gaxi_fifo_async #(
    .DATA_WIDTH(32),
    .DEPTH(16),
    .N_FLOP_CROSS(3)      // 3-stage synchronizer
) u_cdc (
    .axi_wr_aclk(clk_a),
    .axi_wr_aresetn(rst_a_n),
    .wr_valid(domain_a_valid),
    .wr_ready(domain_a_ready),
    .wr_data(domain_a_data),
    .axi_rd_aclk(clk_b),
    .axi_rd_aresetn(rst_b_n),
    .rd_valid(domain_b_valid),
    .rd_ready(domain_b_ready),
    .rd_data(domain_b_data)
);
```

---

## Performance Characteristics

### Latency

| Module | Empty Latency | Full Latency | Notes |
|--------|---------------|--------------|-------|
| gaxi_skid_buffer | 0 cycles | 1 cycle | Zero-latency bypass when empty |
| gaxi_fifo_sync (mux) | 1 cycle | 1 cycle | Combinatorial read |
| gaxi_fifo_sync (flop) | 2 cycles | 2 cycles | Registered read |
| gaxi_fifo_async | 3-5 cycles | 3-5 cycles | CDC synchronization overhead |
| gaxi_drop_fifo_sync | 1 cycle | 1 cycle | Plus 3 cycles for drop operation |

### Throughput

All modules support **1 transfer per clock cycle** when not applying backpressure.

### Resource Utilization (Typical)

| Module | Logic | Memory | Notes |
|--------|-------|--------|-------|
| gaxi_skid_buffer (D=4, DW=32) | ~50 LUTs | 128 FFs | Shift register |
| gaxi_fifo_sync (D=16, DW=32) | ~100 LUTs | 512 FFs | + counters |
| gaxi_fifo_async (D=16, DW=32) | ~150 LUTs | 512 FFs | + CDC logic |
| gaxi_drop_fifo_sync (D=64, DW=32) | ~200 LUTs | 2048 FFs | + drop control |

---

## Common Use Cases

### Video Processing (Skid Buffer)

**Characteristics:**
- High throughput (pixel streams)
- Minimal latency required
- Regular flow control

**Recommended:**
```systemverilog
gaxi_skid_buffer #(
    .DATA_WIDTH(96),    // 4 pixels x 24-bit RGB
    .DEPTH(4)           // Shallow buffer
)
```

### Network Packet Processing (Drop FIFO)

**Characteristics:**
- Variable packet sizes
- Need to drop oldest on overflow
- High data rate

**Recommended:**
```systemverilog
gaxi_drop_fifo_sync #(
    .DATA_WIDTH(512),   // Wide data bus
    .DEPTH(64),         // Deep buffer
    .REGISTERED(1)      // Flop mode for timing
)
```

### Clock Domain Crossing (Async FIFO)

**Characteristics:**
- Independent clock domains
- Metastability protection required
- Variable clock ratios

**Recommended:**
```systemverilog
gaxi_fifo_async #(
    .DATA_WIDTH(32),
    .DEPTH(16),         // Must be power of 2
    .N_FLOP_CROSS(3)    // 3-stage synchronizer
)
```

---

## Parameter Selection Guidelines

### Buffer Depth (DEPTH)

| Application | Recommended Depth | Rationale |
|-------------|-------------------|-----------|
| Pipeline stage | 2-4 | Minimal latency, timing closure |
| Video line buffer | 16-32 | Line-sized bursts |
| Network packet buffer | 32-64 | Variable packet sizes |
| CDC buffer | 8-16 | Handle clock ratio variations |

### Output Mode (REGISTERED)

**Mux Mode (REGISTERED=0):**
- ✅ Lower latency (1 cycle)
- ✅ Smaller area
- ❌ May not meet timing with wide data
- **Use for:** Narrow data (≤64 bits), non-critical paths

**Flop Mode (REGISTERED=1):**
- ✅ Better timing (registered output)
- ✅ Supports wide data
- ❌ Higher latency (2 cycles)
- ❌ More area
- **Use for:** Wide data (≥128 bits), critical paths

### CDC Synchronizer Stages (N_FLOP_CROSS)

| Stages | Use Case |
|--------|----------|
| 2 | Slow clocks (<100 MHz), low risk |
| 3 | **Recommended default** |
| 4+ | High-speed (>400 MHz) or high-reliability |

---

## Related Documentation

### Comprehensive Guide

- **[GAXI Index (Detailed)](index.md)** - Comprehensive guide with timing diagrams

### Protocol Specifications

- ARM AMBA AXI4-Stream Protocol Specification (similar handshake)

### RTL Design Sherpa Documentation

- **[RTLAmba Overview](../overview.md)** - Complete AMBA subsystem architecture
- **[AXI4 Modules](../axi4/README.md)** - Full AXI4 protocol
- **[AXIS4 Modules](../axis4/README.md)** - AXI4-Stream protocol
- **[GAXI WaveDrom Tutorial](../../TestTutorial/wavedrom_gaxi_example.md)** - Timing diagrams

### Source Code

- RTL: `rtl/amba/gaxi/`
- Tests: `val/amba/test_gaxi*.py`
- Framework: `bin/CocoTBFramework/components/gaxi/`

---

## Design Notes

### When to Use GAXI vs AXI4-Stream

**✅ Use GAXI For:**
- Internal buffering and timing closure
- Simple data streaming
- CDC with basic handshake
- Infrastructure/glue logic

**✅ Use AXI4-Stream For:**
- External interfaces
- Need TID/TDEST/TUSER signals
- Complex routing requirements
- Standards compliance

### Buffer vs FIFO Selection

**Use Skid Buffer (gaxi_skid_buffer) When:**
- ✅ Need zero-latency bypass
- ✅ Shallow depth (2-8 entries)
- ✅ Timing closure only
- ✅ Minimal area

**Use FIFO (gaxi_fifo_sync) When:**
- ✅ Need deeper buffering (16+ entries)
- ✅ Rate adaptation required
- ✅ Burst traffic handling
- ✅ More predictable latency

**Use Async FIFO (gaxi_fifo_async) When:**
- ✅ Clock domain crossing required
- ✅ Independent clock domains
- ✅ Need CDC-safe handshake

**Use Drop FIFO (gaxi_drop_fifo_sync) When:**
- ✅ Need to discard oldest data on overflow
- ✅ Packet-based processing
- ✅ Flush/reset functionality required

---

## Common Issues and Debugging

### Issue 1: Data Loss

**Symptom:** Missing data at output

**Debug:**
1. Check `count` signal - should not overflow (reach DEPTH)
2. Verify `wr_valid` stays high until `wr_ready` asserts
3. Increase DEPTH if necessary
4. Add backpressure handling upstream

### Issue 2: Timing Violation

**Symptom:** Setup/hold violations in synthesis

**Solutions:**
1. Use flop mode: `.REGISTERED(1)`
2. Increase DEPTH for better buffering
3. Add pipeline stages with multiple skid buffers

### Issue 3: CDC Metastability

**Symptom:** Incorrect data, simulation/silicon mismatch

**Solutions:**
1. Increase `N_FLOP_CROSS` (minimum 3 recommended)
2. Verify independent clock domains (no relationship)
3. Check reset synchronization in both domains
4. Use constraints for CDC paths

---

**Last Updated:** 2025-10-20

---

## Navigation

- **[← Back to RTLAmba Index](../README.md)**
- **[← Back to Main Documentation Index](../../index.md)**
