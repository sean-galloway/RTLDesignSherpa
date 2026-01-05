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

**[← Back to RTLAmba Index](../index.md)** | **[Main Index](../../index.md)**

# GAXI (Generic AXI) Interface Modules

**Protocol:** Generic AXI-Stream-like handshake interface
**Location:** `rtl/amba/gaxi/`
**Status:** ✅ Production Ready

---

## Overview

GAXI (Generic AXI) is a simplified valid/ready handshake protocol used for streaming data between components. It provides a lightweight interface that's simpler than full AXI-Stream while maintaining robust flow control.

### Key Features

- **Simple Handshake:** `valid`/`ready` only - minimal overhead
- **Elastic Buffering:** Skid buffers and FIFOs for timing closure
- **Clock Domain Crossing:** Async variants with proper CDC
- **Zero-Latency Bypass:** Skid buffer mode for low-latency paths
- **Parameterized:** Configurable data width and depth

---

## Modules

| Module | Purpose | Clock Domains | Key Features |
|--------|---------|---------------|--------------|
| [gaxi_skid_buffer.sv](gaxi_skid_buffer.md) | Elastic buffer with zero-latency bypass | Single | Depth 2-8, combinatorial read |
| [gaxi_fifo_sync.sv](gaxi_fifo_sync.md) | Synchronous FIFO | Single | Any depth, mux/flop modes |
| [gaxi_fifo_async.sv](gaxi_fifo_async.md) | Asynchronous FIFO | Dual (wr/rd) | Gray code pointers, CDC-safe |
| [gaxi_skid_buffer_async.sv](gaxi_skid_buffer_async.md) | Async elastic buffer | Dual (wr/rd) | Combines skid + async FIFO |

---

## Protocol Specification

### Interface Signals

**Write Interface (Master/Source):**
```systemverilog
input  logic          wr_valid,  // Data valid from source
output logic          wr_ready,  // Ready to accept data
input  logic [DW-1:0] wr_data,   // Data from source
```

**Read Interface (Slave/Sink):**
```systemverilog
output logic          rd_valid,  // Data valid to sink
input  logic          rd_ready,  // Ready to accept data from sink
output logic [DW-1:0] rd_data,   // Data to sink
```

**Optional Monitoring:**
```systemverilog
output logic [3:0] count,     // Current FIFO occupancy
output logic [3:0] rd_count,  // Read-side count (skid buffer)
```

### Handshake Rules

1. **Data Transfer:**
   - Transfer occurs when `valid` AND `ready` both asserted
   - `data` must be stable when `valid` is high

2. **Backpressure:**
   - `ready` may go low to apply backpressure
   - `valid` must remain high until transfer completes

3. **Zero-Latency (Skid Buffer):**
   - When empty: `wr_data` appears at `rd_data` immediately
   - When nearly full: Elastic buffering prevents stalls

### Timing Diagrams

See [GAXI WaveDrom Tutorial](../../TestTutorial/wavedrom_gaxi_example.md) for comprehensive timing examples.

---

## Usage Examples

### Example 1: Simple Skid Buffer

```systemverilog
gaxi_skid_buffer #(
    .DATA_WIDTH(32),
    .DEPTH(4)
) u_skid (
    .axi_aclk    (clk),
    .axi_aresetn (rst_n),
    // Write port
    .wr_valid    (src_valid),
    .wr_ready    (src_ready),
    .wr_data     (src_data),
    // Read port
    .rd_valid    (dst_valid),
    .rd_ready    (dst_ready),
    .rd_data     (dst_data),
    // Status
    .count       (fifo_count),
    .rd_count    ()
);
```

### Example 2: Synchronous FIFO

```systemverilog
gaxi_fifo_sync #(
    .DATA_WIDTH(64),
    .DEPTH(16),
    .REGISTERED(0)  // 0=mux mode, 1=flop mode
) u_fifo (
    .axi_aclk    (clk),
    .axi_aresetn (rst_n),
    .wr_valid    (wr_valid),
    .wr_ready    (wr_ready),
    .wr_data     (wr_data),
    .rd_ready    (rd_ready),
    .rd_valid    (rd_valid),
    .rd_data     (rd_data),
    .count       (count)
);
```

### Example 3: Clock Domain Crossing

```systemverilog
gaxi_fifo_async #(
    .DATA_WIDTH(32),
    .DEPTH(8),
    .N_FLOP_CROSS(3),  // CDC synchronizer stages
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
    .rd_ready       (rd_ready),
    .rd_valid       (rd_valid),
    .rd_data        (rd_data)
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

### Throughput

All modules support **1 transfer per clock cycle** when not applying backpressure.

### Resource Utilization

| Module | Logic | Memory | Notes |
|--------|-------|--------|-------|
| gaxi_skid_buffer (D=4) | ~50 LUTs | 4×DW flops | Shift register |
| gaxi_fifo_sync (D=16) | ~100 LUTs | 16×DW flops | + counters |
| gaxi_fifo_async (D=16) | ~150 LUTs | 16×DW flops | + CDC logic |

---

## Design Patterns

### Pattern 1: Timing Closure (Pipeline Stage)

Use skid buffer to break combinatorial paths:

```systemverilog
// Without skid buffer: long combinatorial path
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
    .wr_valid(bursty_valid),  // Intermittent bursts
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
    .DEPTH(8),
    .N_FLOP_CROSS(3)
) u_cdc (
    .axi_wr_aclk(clk_a),
    .axi_wr_aresetn(rst_a_n),
    .wr_valid(domain_a_valid),
    .wr_ready(domain_a_ready),
    .wr_data(domain_a_data),
    .axi_rd_aclk(clk_b),
    .axi_rd_aresetn(rst_b_n),
    .rd_ready(domain_b_ready),
    .rd_valid(domain_b_valid),
    .rd_data(domain_b_data)
);
```

---

## Testing

### Test Coverage

| Test | File | Coverage |
|------|------|----------|
| Synchronous Buffer | `val/amba/test_gaxi_buffer_sync.py` | Functional, stress, randomization |
| Asynchronous Buffer | `val/amba/test_gaxi_buffer_async.py` | CDC, clock ratios, stress |
| WaveDrom Example | `val/amba/test_gaxi_wavedrom_example.py` | Timing diagrams, 6 scenarios |

### Running Tests

```bash
# Synchronous tests (all modes: skid, fifo_mux, fifo_flop)
pytest val/amba/test_gaxi_buffer_sync.py -v

# Asynchronous tests (CDC with various clock ratios)
pytest val/amba/test_gaxi_buffer_async.py -v

# Generate waveforms
pytest val/amba/test_gaxi_wavedrom_example.py -v
cd val/amba && bash wd_cmd.sh  # Generate PNG/SVG
```

---

## Common Issues and Debugging

### Issue 1: Data Loss

**Symptom:** Packets missing at output

**Debug Steps:**
1. Check `count` signal - should not overflow
2. Verify `valid` stays high until `ready` asserts
3. Increase FIFO depth if necessary

### Issue 2: Backpressure Not Working

**Symptom:** `wr_ready` never goes low

**Debug Steps:**
1. Check DEPTH parameter matches requirements
2. Verify read side is actually consuming data
3. Look at `count` signal - should reach DEPTH

### Issue 3: CDC Violations (Async FIFO)

**Symptom:** Metastability, incorrect data

**Debug Steps:**
1. Increase N_FLOP_CROSS (minimum 3 recommended)
2. Verify independent clock domains (no relationship)
3. Check reset timing - both domains must reset properly

---

## References

- **Tutorial:** [GAXI WaveDrom Tutorial](../../TestTutorial/wavedrom_gaxi_example.md)
- **Source:** `rtl/amba/gaxi/`
- **Tests:** `val/amba/test_gaxi_*.py`
- **Dependencies:** `rtl/common/counter_bin.sv`, `rtl/common/fifo_control.sv`

---

**Version:** 1.0
**Last Updated:** 2025-10-06
**Maintained By:** RTL Design Sherpa Project
