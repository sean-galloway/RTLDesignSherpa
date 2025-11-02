# GAXI Asynchronous FIFO

**Module:** `gaxi_fifo_async.sv`
**Location:** `rtl/amba/gaxi/`
**Status:** ✅ Production Ready

---

## Overview

The GAXI asynchronous FIFO enables safe clock domain crossing (CDC) between independent clock domains. It uses Gray code pointers and multi-flop synchronizers to prevent metastability and ensure data integrity.

### Key Features

- ✅ **Clock Domain Crossing:** Safe transfer between independent clocks
- ✅ **Gray Code Pointers:** Prevents multi-bit synchronization issues
- ✅ **Configurable CDC Stages:** 2-3 flop synchronizers (3 recommended)
- ✅ **Arbitrary Clock Ratios:** Works with any write:read clock ratio
- ✅ **Two Read Modes:** Mux or Flop mode

---

## Module Interface

```systemverilog
module gaxi_fifo_async #(
    parameter int REGISTERED = 0,         // 0=mux mode, 1=flop mode
    parameter int DATA_WIDTH = 8,
    parameter int DEPTH = 10,
    parameter int N_FLOP_CROSS = 2,      // CDC synchronizer stages
    parameter int ALMOST_WR_MARGIN = 1,
    parameter int ALMOST_RD_MARGIN = 1,
    parameter     INSTANCE_NAME = "DEADF1F0"
) (
    // Write Domain
    input  logic            axi_wr_aclk,
    input  logic            axi_wr_aresetn,
    input  logic            wr_valid,
    output logic            wr_ready,    // not full
    input  logic [DW-1:0]   wr_data,
    
    // Read Domain
    input  logic            axi_rd_aclk,
    input  logic            axi_rd_aresetn,
    input  logic            rd_ready,
    output logic            rd_valid,    // not empty
    output logic [DW-1:0]   rd_data
);
```

---

## Parameters

| Parameter | Default | Description |
|-----------|---------|-------------|
| `REGISTERED` | 0 | 0=mux mode, 1=flop mode (read path) |
| `DATA_WIDTH` | 8 | Data bus width |
| `DEPTH` | 10 | FIFO depth (even values recommended) |
| `N_FLOP_CROSS` | 2 | Synchronizer stages (3 recommended for safety) |
| `ALMOST_WR_MARGIN` | 1 | Almost full threshold |
| `ALMOST_RD_MARGIN` | 1 | Almost empty threshold |

**⚠️ Important:** Set `N_FLOP_CROSS=3` for production designs to ensure metastability protection.

---

## Functional Description

### Clock Domain Crossing Architecture

```
Write Domain                      Read Domain
┌──────────────┐                 ┌──────────────┐
│ wr_ptr (bin) │                 │ rd_ptr (bin) │
│      ↓       │                 │      ↓       │
│ wr_ptr (Gray)│────┐       ┌────│ rd_ptr (Gray)│
└──────────────┘    │       │    └──────────────┘
                    │       │
                ┌───▼───────▼───┐
                │  Gray Code    │
                │ Synchronizers │
                │ (N_FLOP_CROSS)│
                └───┬───────┬───┘
                    │       │
┌──────────────┐    │       │    ┌──────────────┐
│ rd_ptr_sync  │◄───┘       └───►│ wr_ptr_sync  │
│ (in wr_clk)  │                 │ (in rd_clk)  │
│      ↓       │                 │      ↓       │
│ Full Logic   │                 │ Empty Logic  │
└──────────────┘                 └──────────────┘
```

### Why Gray Code?

Gray code ensures only one bit changes at a time during pointer updates:

```
Binary: 011 → 100  (2 bits change - hazard!)
Gray:   010 → 110  (1 bit changes - safe!)
```

This prevents glitches during synchronization across clock domains.

### Dependencies

- `counter_bin.sv` - Binary counters
- `counter_johnson.sv` - Gray code (Johnson) counters
- `glitch_free_n_dff_arn.sv` - Multi-flop synchronizers
- `grayj2bin.sv` - Gray-to-binary conversion
- `fifo_control.sv` - Full/empty flag generation

---

## Usage Examples

### Example 1: Basic CDC FIFO

```systemverilog
gaxi_fifo_async #(
    .DATA_WIDTH(32),
    .DEPTH(16),
    .N_FLOP_CROSS(3),      // 3-stage synchronizer
    .REGISTERED(0)
) u_cdc_fifo (
    // Write domain @ 100 MHz
    .axi_wr_aclk    (clk_100mhz),
    .axi_wr_aresetn (rst_100_n),
    .wr_valid       (domain_a_valid),
    .wr_ready       (domain_a_ready),
    .wr_data        (domain_a_data),
    
    // Read domain @ 50 MHz
    .axi_rd_aclk    (clk_50mhz),
    .axi_rd_aresetn (rst_50_n),
    .rd_ready       (domain_b_ready),
    .rd_valid       (domain_b_valid),
    .rd_data        (domain_b_data)
);
```

### Example 2: High-Speed to Low-Speed CDC

```systemverilog
// Fast writer (250 MHz) → Slow reader (62.5 MHz)
// Needs deeper FIFO to handle burst traffic
gaxi_fifo_async #(
    .DATA_WIDTH(64),
    .DEPTH(32),           // Deeper for rate mismatch
    .N_FLOP_CROSS(3),
    .REGISTERED(1)        // Flop mode for timing
) u_rate_converter (
    .axi_wr_aclk    (clk_250mhz),
    .axi_wr_aresetn (rst_fast_n),
    .wr_valid       (fast_valid),
    .wr_ready       (fast_ready),
    .wr_data        (fast_data),
    
    .axi_rd_aclk    (clk_62p5mhz),
    .axi_rd_aresetn (rst_slow_n),
    .rd_ready       (slow_ready),
    .rd_valid       (slow_valid),
    .rd_data        (slow_data)
);
```

---

## Timing Characteristics

| Clock Ratio (wr:rd) | Latency | Notes |
|---------------------|---------|-------|
| 1:1 (same freq) | 3-5 cycles | CDC synchronization overhead |
| 2:1 (fast→slow) | 4-6 cycles | Additional write-side delay |
| 1:2 (slow→fast) | 3-5 cycles | Read-side samples faster |
| Any ratio | 3-7 cycles | Depends on synchronizer stages + clock relationship |

**Latency Formula:** `~(2 × N_FLOP_CROSS) + 1` in slower clock domain cycles

---

## Design Considerations

### Depth Sizing for Clock Ratio

When write clock >> read clock, size FIFO to handle burst accumulation:

```
Required Depth ≥ Burst Size × (Write Freq / Read Freq) × Safety Margin

Example:
- Write: 100 MHz, Read: 25 MHz
- Burst: 16 transfers
- Safety: 1.5x
→ Depth ≥ 16 × (100/25) × 1.5 = 96 entries
```

### Reset Synchronization

**Critical:** Both clock domains must have properly synchronized resets!

```systemverilog
// Separate reset synchronizers for each domain
reset_sync u_wr_rst_sync (
    .clk(axi_wr_aclk),
    .async_rst_n(global_rst_n),
    .sync_rst_n(axi_wr_aresetn)
);

reset_sync u_rd_rst_sync (
    .clk(axi_rd_aclk),
    .async_rst_n(global_rst_n),
    .sync_rst_n(axi_rd_aresetn)
);
```

### Metastability Protection

`N_FLOP_CROSS` determines MTBF (Mean Time Between Failures):

| Stages | MTBF (typical @ 100 MHz) | Use Case |
|--------|-------------------------|----------|
| 2 | ~years | Short-term prototyping only |
| 3 | ~centuries | **Production standard** |
| 4 | ~millennia | Ultra-critical systems |

**Recommendation:** Always use `N_FLOP_CROSS=3` in production.

---

## Error Checking

Simulation-only assertions catch protocol violations:

```systemverilog
// Write domain checks
always @(posedge axi_wr_aclk) begin
    if (!axi_wr_aresetn && wr_valid && !wr_ready) begin
        $display("Error: %s write while FIFO full", INSTANCE_NAME);
    end
end

// Read domain checks
always @(posedge axi_rd_aclk) begin
    if (!axi_rd_aresetn && rd_ready && !rd_valid) begin
        $display("Error: %s read while FIFO empty", INSTANCE_NAME);
    end
end
```

---

## Testing

```bash
# Async FIFO tests with various clock ratios
pytest val/amba/test_gaxi_buffer_async.py -v

# Test specific clock ratio (wr:rd)
pytest val/amba/test_gaxi_buffer_async.py -k "wr10_rd12" -v  # 10ns : 12ns
```

Test matrix includes:
- Same clocks (1:1)
- 1.25x ratio (10ns : 12ns)
- 2x ratio (10ns : 20ns)
- 2.5x ratio (8ns : 20ns)

---

## Common Issues

### Issue 1: Metastability

**Symptom:** Random data corruption, simulation/hardware mismatch

**Solution:** Increase `N_FLOP_CROSS` to 3 or 4

### Issue 2: Pointer Synchronization Failure

**Symptom:** FIFO full/empty signals incorrect

**Debug:**
1. Verify clocks are truly independent (no PLL relationship violations)
2. Check reset synchronization - both domains must reset properly
3. Verify Gray code conversion logic

### Issue 3: Underflow/Overflow

**Symptom:** Data loss or corruption

**Debug:**
1. Check DEPTH is sufficient for clock ratio
2. Verify flow control respected in both domains
3. Monitor pointer values in both domains

---

## Related Modules

- [gaxi_fifo_sync](gaxi_fifo_sync.md) - Single clock domain version
- [gaxi_skid_buffer_async](gaxi_skid_buffer_async.md) - Async skid buffer
- [GAXI Index](index.md) - Overview

---

## References

- **Clifford Cummings:** "Simulation and Synthesis Techniques for Asynchronous FIFO Design" (Sunburst Design)
- **Source:** `rtl/amba/gaxi/gaxi_fifo_async.sv`
- **Tests:** `val/amba/test_gaxi_buffer_async.py`

---

**Version:** 1.0
**Last Updated:** 2025-10-06
