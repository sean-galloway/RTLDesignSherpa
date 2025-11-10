# AXI4 ↔ AXI4-Lite Protocol Converters

**Location:** `projects/components/converters/rtl/`
**Created:** 2025-11-05
**Status:** Functional - Ready for integration and testing

---

## Overview

Protocol converters between AXI4 Full and AXI4-Lite in both directions.

**✅ Recommended: Use split read/write modules** for most applications (saves area, easier integration)

### Module Variants

| Module | Channels | Direction | Purpose |
|--------|----------|-----------|---------|
| **Split Modules (Recommended)** |
| `axi4_to_axil4_rd.sv` | AR, R | AXI4 → Lite (Read only) | Most common - read-only paths |
| `axi4_to_axil4_wr.sv` | AW, W, B | AXI4 → Lite (Write only) | Write-only paths |
| `axil4_to_axi4_rd.sv` | AR, R | Lite → AXI4 (Read only) | Protocol upgrade (read) |
| `axil4_to_axi4_wr.sv` | AW, W, B | Lite → AXI4 (Write only) | Protocol upgrade (write) |
| **Combined Modules (Legacy)** |
| `axi4_to_axil4.sv` | All | AXI4 → Lite (Bidirectional) | Both read and write |
| `axil4_to_axi4.sv` | All | Lite → AXI4 (Bidirectional) | Both read and write |

### When to Use Which?

**Use Split Modules (Recommended):**
- ✅ Read-only interfaces (most peripherals)
- ✅ Write-only interfaces (some accelerators)
- ✅ Smaller area (instantiate only what you need)
- ✅ Clearer intent in design
- ✅ Easier to verify

**Use Combined Modules:**
- ⚠️ When you truly need bidirectional conversion
- ⚠️ When area is not a concern
- ⚠️ Quick prototyping

---

## Split Modules (Recommended)

### axi4_to_axil4_rd.sv - Read Path Only

**Purpose:** Convert AXI4 full → AXI4-Lite (READ ONLY)

**Features:**
- Read burst decomposition (AR, R channels)
- Same functionality as combined module, but read-only
- Smaller area (50% reduction vs. combined)
- State machine for burst tracking

**Example:**
```systemverilog
axi4_to_axil4_rd #(
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64)
) u_rd_converter (
    .aclk(clk), .aresetn(rst_n),
    // AXI4 slave (read only)
    .s_axi_arid(dma_arid),
    .s_axi_araddr(dma_araddr),
    .s_axi_arlen(dma_arlen),
    // ... AR channel
    .s_axi_rid(dma_rid),
    .s_axi_rdata(dma_rdata),
    // ... R channel
    // AXI4-Lite master (read only)
    .m_axil_araddr(reg_araddr),
    .m_axil_arprot(reg_arprot),
    .m_axil_arvalid(reg_arvalid),
    .m_axil_arready(reg_arready),
    .m_axil_rdata(reg_rdata),
    .m_axil_rresp(reg_rresp),
    .m_axil_rvalid(reg_rvalid),
    .m_axil_rready(reg_rready)
);
```

---

### axi4_to_axil4_wr.sv - Write Path Only

**Purpose:** Convert AXI4 full → AXI4-Lite (WRITE ONLY)

**Features:**
- Write burst decomposition (AW, W, B channels)
- Same functionality as combined module, but write-only
- Smaller area (50% reduction vs. combined)
- State machine for burst tracking

**Example:**
```systemverilog
axi4_to_axil4_wr #(
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64)
) u_wr_converter (
    .aclk(clk), .aresetn(rst_n),
    // AXI4 slave (write only)
    .s_axi_awid(dma_awid),
    .s_axi_awaddr(dma_awaddr),
    // ... AW channel
    .s_axi_wdata(dma_wdata),
    .s_axi_wstrb(dma_wstrb),
    // ... W channel
    .s_axi_bid(dma_bid),
    .s_axi_bresp(dma_bresp),
    // ... B channel
    // AXI4-Lite master (write only)
    .m_axil_awaddr(reg_awaddr),
    .m_axil_awprot(reg_awprot),
    // ... AW, W, B channels
);
```

---

### axil4_to_axi4_rd.sv - Read Path Only

**Purpose:** Convert AXI4-Lite → AXI4 full (READ ONLY)

**Features:**
- Simple passthrough with field additions (AR, R channels)
- Minimal overhead
- Smaller area (50% reduction vs. combined)

**Example:**
```systemverilog
axil4_to_axi4_rd #(
    .AXI_ID_WIDTH(4),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(32),
    .DEFAULT_ID(1)  // Assign unique ID
) u_rd_upgrade (
    .aclk(clk), .aresetn(rst_n),
    // AXI4-Lite slave (read only)
    .s_axil_araddr(cpu_araddr),
    .s_axil_arprot(cpu_arprot),
    .s_axil_arvalid(cpu_arvalid),
    .s_axil_arready(cpu_arready),
    .s_axil_rdata(cpu_rdata),
    .s_axil_rresp(cpu_rresp),
    .s_axil_rvalid(cpu_rvalid),
    .s_axil_rready(cpu_rready),
    // AXI4 master (read only)
    .m_axi_arid(xbar_arid),
    .m_axi_araddr(xbar_araddr),
    .m_axi_arlen(xbar_arlen),
    // ... Full AR channel with defaults
    .m_axi_rid(xbar_rid),
    .m_axi_rdata(xbar_rdata),
    // ... R channel
);
```

---

### axil4_to_axi4_wr.sv - Write Path Only

**Purpose:** Convert AXI4-Lite → AXI4 full (WRITE ONLY)

**Features:**
- Simple passthrough with field additions (AW, W, B channels)
- Minimal overhead
- Smaller area (50% reduction vs. combined)

**Example:**
```systemverilog
axil4_to_axi4_wr #(
    .AXI_ID_WIDTH(4),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(32),
    .DEFAULT_ID(1)
) u_wr_upgrade (
    .aclk(clk), .aresetn(rst_n),
    // AXI4-Lite slave (write only)
    .s_axil_awaddr(cpu_awaddr),
    .s_axil_awprot(cpu_awprot),
    // ... AW, W, B channels
    // AXI4 master (write only)
    .m_axi_awid(xbar_awid),
    .m_axi_awaddr(xbar_awaddr),
    .m_axi_awlen(xbar_awlen),
    // ... Full AW, W, B channels with defaults
);
```

---

## Combined Modules (Legacy - Use Split Modules Instead)

### Module 1: axi4_to_axil4.sv

**Purpose:** Convert AXI4 full protocol to AXI4-Lite

### Features

- **Burst Decomposition:** Multi-beat bursts → multiple single-beat transactions
- **Address Increment:** Handles INCR, FIXED, WRAP burst types
- **Response Aggregation:** Accumulates responses from decomposed beats
- **Protocol Stripping:** Removes ID, USER, REGION, QOS fields
- **Timing Closure:** State machines with proper reset handling

### Key Behaviors

#### Read Path
```
AXI4 Input              Converter                  AXI4-Lite Output
─────────────           ─────────────             ──────────────────
AR: LEN=7 (8 beats) →   Decompose into 8 txns  → AR: 8 separate addr
                        Increment address
R: 8 data beats     ←   Aggregate responses    ← R: 8 single responses
   RLAST on beat 8      Return with original ID
```

#### Write Path
```
AXI4 Input              Converter                  AXI4-Lite Output
─────────────           ─────────────             ──────────────────
AW: LEN=3 (4 beats) →   Decompose into 4 txns  → AW: 4 separate addr
W: 4 data beats     →                          → W: 4 single writes
B: 1 response       ←   Aggregate responses    ← B: 4 responses
   Return with original ID
```

### Parameters

```systemverilog
axi4_to_axil4 #(
    .AXI_ID_WIDTH(8),        // ID width (1-16)
    .AXI_ADDR_WIDTH(32),     // Address width
    .AXI_DATA_WIDTH(64),     // Data width (must match)
    .AXI_USER_WIDTH(1),      // User signal width
    .SKID_DEPTH_AR(2),       // AR channel buffer depth
    .SKID_DEPTH_AW(2),       // AW channel buffer depth
    .SKID_DEPTH_W(4),        // W channel buffer depth
    .SKID_DEPTH_R(4),        // R channel buffer depth
    .SKID_DEPTH_B(4)         // B channel buffer depth
) u_axi4_to_axil4 (
    // AXI4 slave interface
    .s_axi_ar*(...),
    .s_axi_r*(...),
    .s_axi_aw*(...),
    .s_axi_w*(...),
    .s_axi_b*(...),
    // AXI4-Lite master interface
    .m_axil_ar*(...),
    .m_axil_r*(...),
    .m_axil_aw*(...),
    .m_axil_w*(...),
    .m_axil_b*(...)
);
```

### Use Cases

- **Legacy Integration:** Connect AXI4 master to AXI4-Lite-only peripheral
- **Bandwidth Reduction:** Simplify protocol when burst not needed
- **Register Access:** Convert burst-capable master to simple register interface

### Limitations

- Data widths must match (no width conversion)
- Throughput reduced (N-beat burst → N separate transactions)
- Latency increased (sequential transactions vs. pipeline)

---

## Module 2: axil4_to_axi4.sv

**Purpose:** Convert AXI4-Lite to AXI4 full protocol

### Features

- **Protocol Upgrade:** Add AXI4-only fields with safe defaults
- **Simple Passthrough:** All transactions remain single-beat
- **Configurable Defaults:** ID, REGION, QOS values
- **Minimal Overhead:** Direct signal mapping where possible

### Key Behaviors

#### Read Path
```
AXI4-Lite Input         Converter                  AXI4 Output
─────────────          ─────────────              ──────────────
AR: addr, prot      →  Add ID=0, LEN=0, etc.  →  AR: Full AXI4 signals
R: data, resp       ←  Strip ID, LAST, USER   ←  R: data, resp, RLAST=1
```

#### Write Path
```
AXI4-Lite Input         Converter                  AXI4 Output
─────────────          ─────────────              ──────────────
AW: addr, prot      →  Add ID=0, LEN=0, etc.  →  AW: Full AXI4 signals
W: data, strb       →  Add WLAST=1            →  W: data, strb, WLAST=1
B: resp             ←  Strip ID, USER         ←  B: resp, BID
```

### Default Values Added

| Field | Default Value | Description |
|-------|---------------|-------------|
| ARID/AWID | `DEFAULT_ID` (param) | Transaction ID |
| ARLEN/AWLEN | `8'd0` | Single beat |
| ARSIZE/AWSIZE | `$clog2(DATA_WIDTH/8)` | Full width |
| ARBURST/AWBURST | `2'b01` | INCR type |
| ARLOCK/AWLOCK | `1'b0` | Normal access |
| ARCACHE/AWCACHE | `4'b0011` | Bufferable |
| ARQOS/AWQOS | `DEFAULT_QOS` (param) | Quality of Service |
| ARREGION/AWREGION | `DEFAULT_REGION` (param) | Memory region |
| ARUSER/AWUSER | `'0` | No user data |
| WLAST | `1'b1` | Always last |
| WUSER | `'0` | No user data |

### Parameters

```systemverilog
axil4_to_axi4 #(
    .AXI_ID_WIDTH(8),        // ID width (1-16)
    .AXI_ADDR_WIDTH(32),     // Address width
    .AXI_DATA_WIDTH(64),     // Data width (must match)
    .AXI_USER_WIDTH(1),      // User signal width
    .DEFAULT_ID(0),          // Default transaction ID
    .DEFAULT_REGION(0),      // Default region
    .DEFAULT_QOS(0),         // Default QoS
    .SKID_DEPTH_AR(2),       // AR channel buffer depth
    .SKID_DEPTH_AW(2),       // AW channel buffer depth
    .SKID_DEPTH_W(4),        // W channel buffer depth
    .SKID_DEPTH_R(4),        // R channel buffer depth
    .SKID_DEPTH_B(4)         // B channel buffer depth
) u_axil4_to_axi4 (
    // AXI4-Lite slave interface
    .s_axil_ar*(...),
    .s_axil_r*(...),
    .s_axil_aw*(...),
    .s_axil_w*(...),
    .s_axil_b*(...),
    // AXI4 master interface
    .m_axi_ar*(...),
    .m_axi_r*(...),
    .m_axi_aw*(...),
    .m_axi_w*(...),
    .m_axi_b*(...)
);
```

### Use Cases

- **Interconnect Integration:** Connect AXI4-Lite master to AXI4 crossbar/interconnect
- **Protocol Compatibility:** Interface simple master with full AXI4 slaves
- **System Integration:** Mix AXI4-Lite and AXI4 components in same design

### Limitations

- Data widths must match (no width conversion)
- No burst generation (all transactions single-beat)
- Cannot utilize AXI4 burst performance features

---

## Design Patterns

### Pattern 1: AXI4 Master to AXI4-Lite Slave

```systemverilog
// High-performance DMA → Simple register bank
axi4_to_axil4 #(
    .AXI_ID_WIDTH(4),
    .AXI_ADDR_WIDTH(16),
    .AXI_DATA_WIDTH(32)
) u_bridge (
    .aclk(clk), .aresetn(rst_n),
    // DMA master (AXI4)
    .s_axi_ar*(dma_ar*),
    .s_axi_r*(dma_r*),
    // Register bank slave (AXI4-Lite)
    .m_axil_ar*(reg_ar*),
    .m_axil_r*(reg_r*)
);
```

### Pattern 2: AXI4-Lite Master to AXI4 Interconnect

```systemverilog
// CPU → AXI4 crossbar
axil4_to_axi4 #(
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(32),
    .DEFAULT_ID(5)  // CPU gets ID 5
) u_bridge (
    .aclk(clk), .aresetn(rst_n),
    // CPU (AXI4-Lite)
    .s_axil_ar*(cpu_ar*),
    .s_axil_r*(cpu_r*),
    // Crossbar (AXI4)
    .m_axi_ar*(xbar_ar*),
    .m_axi_r*(xbar_r*)
);
```

### Pattern 3: Bidirectional Bridge Chain

```systemverilog
// Create translation layer for mixed protocol systems
// AXI4 Master → AXI4-Lite → AXI4 Slave

axi4_to_axil4 u_to_lite (...);  // Master side

simple_axil4_fabric u_fabric (...);  // AXI4-Lite interconnect

axil4_to_axi4 u_to_full (...);  // Slave side
```

---

## Implementation Notes

### Reset Handling

Both converters use reset macros from `reset_defs.svh`:
```systemverilog
`include "reset_defs.svh"

`ALWAYS_FF_RST(aclk, aresetn,
    if (`RST_ASSERTED(aresetn)) begin
        // Reset logic
    end else begin
        // Normal operation
    end
)
```

### State Machines (axi4_to_axil4 only)

**Read Path States:**
- `RD_IDLE`: Accept new transaction
- `RD_BURST`: Decomposing multi-beat burst
- `RD_LAST_BEAT`: Final beat of burst

**Write Path States:**
- `WR_IDLE`: Accept new transaction
- `WR_BURST`: Decomposing multi-beat burst
- `WR_LAST_BEAT`: Final beat of burst

### Burst Address Calculation

```systemverilog
// Address increment per beat
addr_incr = (1 << ARSIZE/AWSIZE);

// INCR/WRAP: addr = addr + increment
// FIXED: addr unchanged
```

### Response Accumulation

Both converters accumulate worst-case response:
- SLVERR > DECERR > EXOKAY > OKAY
- Final response returned with original transaction ID

---

## Testing Recommendations

### Test Scenarios

1. **Single-beat transactions** (LEN=0) - passthrough mode
2. **Small bursts** (LEN=3, 7) - decomposition accuracy
3. **Large bursts** (LEN=255) - state machine robustness
4. **All burst types** (FIXED, INCR, WRAP) - address calculation
5. **Error responses** (SLVERR, DECERR) - response propagation
6. **Back-pressure** - handling of ready signals
7. **Concurrent R/W** - independent channel operation

### Verification Checklist

- [ ] Data integrity through conversion
- [ ] Correct address increment for all burst types
- [ ] Response accumulation (worst case)
- [ ] ID preservation through round-trip
- [ ] RLAST/WLAST generation
- [ ] Protocol compliance (AXI4, AXI4-Lite)
- [ ] Reset behavior
- [ ] Corner cases (LEN=0, LEN=255)

---

## Integration Example

### Complete System with Both Converters

```systemverilog
module mixed_protocol_system (
    input  logic clk,
    input  logic rst_n,
    // AXI4 master interface
    axi4_if.slave  axi4_master,
    // AXI4-Lite slave interface
    axil4_if.master axil4_slave
);

    // Internal AXI4-Lite interconnect
    axil4_if axil_internal();

    // AXI4 → AXI4-Lite (master side)
    axi4_to_axil4 #(
        .AXI_ID_WIDTH(8),
        .AXI_ADDR_WIDTH(32),
        .AXI_DATA_WIDTH(64)
    ) u_to_lite (
        .aclk(clk),
        .aresetn(rst_n),
        .s_axi_*(axi4_master),
        .m_axil_*(axil_internal.master)
    );

    // AXI4-Lite internal fabric/routing
    // ... (address decode, arbitration, etc.)

    // AXI4-Lite → AXI4 (slave side, if needed)
    axil4_to_axi4 #(
        .AXI_ID_WIDTH(4),
        .AXI_ADDR_WIDTH(32),
        .AXI_DATA_WIDTH(64),
        .DEFAULT_ID(0)
    ) u_to_full (
        .aclk(clk),
        .aresetn(rst_n),
        .s_axil_*(axil_internal.slave),
        .m_axi_*(axi4_slave)
    );

endmodule
```

---

## Performance Characteristics

### axi4_to_axil4 Throughput

| Input Burst | Output Transactions | Latency Increase |
|-------------|---------------------|------------------|
| 1 beat (LEN=0) | 1 transaction | None (passthrough) |
| 4 beats (LEN=3) | 4 transactions | 3× cycles |
| 8 beats (LEN=7) | 8 transactions | 7× cycles |
| 256 beats (LEN=255) | 256 transactions | 255× cycles |

**Note:** Sequential decomposition reduces throughput but maintains data integrity.

### axil4_to_axi4 Throughput

| Input Transaction | Output Transaction | Overhead |
|-------------------|-------------------|----------|
| 1 read/write | 1 AXI4 transaction | Minimal (signal mapping) |

**Note:** Essentially zero overhead - direct passthrough with field additions.

---

## Future Enhancements

Potential improvements for future versions:

1. **Pipelined Burst Decomposition** - Overlap transactions for better throughput
2. **Data Width Conversion** - Integrate upsizing/downsizing logic
3. **Outstanding Transaction Tracking** - Better ID management
4. **Performance Counters** - Monitor conversion efficiency
5. **Error Injection** - Testing and debug features

---

## References

### Related Modules
- `axi4_dwidth_converter_rd.sv` - AXI4 data width conversion (read)
- `axi4_dwidth_converter_wr.sv` - AXI4 data width conversion (write)
- `axi4_to_apb_convert.sv` - AXI4 to APB protocol conversion
- `rtl/amba/axi4/*.sv` - AXI4 protocol infrastructure
- `rtl/amba/axil4/*.sv` - AXI4-Lite protocol infrastructure

### Documentation
- ARM AMBA AXI4 Specification
- ARM AMBA AXI4-Lite Specification
- `docs/markdown/RTLAmba/` - AMBA protocol documentation
- `/CLAUDE.md` - Repository coding standards

---

## Quick Module Selection Guide

```
Need to connect...                         → Use this module
──────────────────────────────────────────────────────────────────
AXI4 master (read) → AXI4-Lite slave       → axi4_to_axil4_rd.sv
AXI4 master (write) → AXI4-Lite slave      → axi4_to_axil4_wr.sv
AXI4 master (both) → AXI4-Lite slave       → axi4_to_axil4.sv (or instantiate both split modules)

AXI4-Lite master (read) → AXI4 slave       → axil4_to_axi4_rd.sv
AXI4-Lite master (write) → AXI4 slave      → axil4_to_axi4_wr.sv
AXI4-Lite master (both) → AXI4 slave       → axil4_to_axi4.sv (or instantiate both split modules)
```

**General Rule:** Always prefer split modules (_rd.sv or _wr.sv) unless you need both directions.

---

## File Summary

### Split Modules (✅ Use These)
- `axi4_to_axil4_rd.sv` - 9.3 KB - AXI4→Lite read path
- `axi4_to_axil4_wr.sv` - 9.9 KB - AXI4→Lite write path
- `axil4_to_axi4_rd.sv` - 6.0 KB - Lite→AXI4 read path
- `axil4_to_axi4_wr.sv` - 6.9 KB - Lite→AXI4 write path

### Combined Modules (⚠️ Legacy)
- `axi4_to_axil4.sv` - 17 KB - AXI4→Lite bidirectional
- `axil4_to_axi4.sv` - 10 KB - Lite→AXI4 bidirectional

---

**Author:** RTL Design Sherpa
**Created:** 2025-11-05
**Version:** 1.0
