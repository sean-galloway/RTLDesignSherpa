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

# AMBA Protocol Shims

**Location:** `rtl/amba/shims/`
**Test Location:** `val/amba/`, `val/integ_amba/`
**Status:** ✅ Production Ready

---

## Overview

The shims subsystem provides protocol conversion modules that bridge between different bus protocols and interface standards. These adapters enable seamless integration of heterogeneous components within the AMBA ecosystem.

### Key Features

- ✅ **Protocol Bridging:** Convert between AXI4, APB, and custom interfaces
- ✅ **Clock Domain Crossing:** Dual-clock support with proper CDC
- ✅ **Width Adaptation:** Automatic data width conversion
- ✅ **Burst Decomposition:** Complex transactions → Simple protocol transfers
- ✅ **Standards Compliance:** PeakRDL integration, APB/AXI4 conformance
- ✅ **Production Ready:** Comprehensive testing and verification

---

## Available Shims

| Shim | Purpose | Documentation | Status |
|------|---------|---------------|--------|
| **axi4_to_apb_shim** | AXI4 to APB bridge with dual-clock CDC | [axi4_to_apb_shim.md](axi4_to_apb_shim.md) | ✅ Documented |
| **axi4_to_apb_convert** | Core AXI4→APB conversion logic | [axi4_to_apb_convert.md](axi4_to_apb_convert.md) | ✅ Documented |
| **peakrdl_to_cmdrsp** | PeakRDL passthrough → cmd/rsp adapter | [peakrdl_to_cmdrsp.md](peakrdl_to_cmdrsp.md) | ✅ Documented |

---

## Quick Start

### AXI4 to APB Bridge

```systemverilog
// Bridge AXI4 master to APB peripheral bus
axi4_to_apb_shim #(
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(32),
    .APB_ADDR_WIDTH(32),
    .APB_DATA_WIDTH(32)
) u_bridge (
    .aclk(axi_clk),
    .aresetn(axi_resetn),
    .pclk(apb_clk),
    .presetn(apb_resetn),

    // AXI4 slave interface
    .s_axi_awid(axi_awid),
    .s_axi_awaddr(axi_awaddr),
    // ... AXI signals ...

    // APB master interface
    .m_apb_PSEL(apb_psel),
    .m_apb_PADDR(apb_paddr),
    // ... APB signals ...
);
```

### PeakRDL Register Integration

```systemverilog
// Integrate PeakRDL register block
peakrdl_to_cmdrsp #(
    .ADDR_WIDTH(12),
    .DATA_WIDTH(32)
) u_adapter (
    .aclk(clk),
    .aresetn(rst_n),

    // From APB master stub (cmd/rsp)
    .cmd_valid(cmd_valid),
    .cmd_ready(cmd_ready),
    .cmd_pwrite(cmd_pwrite),
    .cmd_paddr(cmd_paddr),
    .cmd_pwdata(cmd_pwdata),
    .cmd_pstrb(cmd_pstrb),
    .rsp_valid(rsp_valid),
    .rsp_ready(rsp_ready),
    .rsp_prdata(rsp_prdata),
    .rsp_pslverr(rsp_pslverr),

    // To PeakRDL register block
    .regblk_req(regblk_req),
    .regblk_req_is_wr(regblk_req_is_wr),
    // ... PeakRDL cpuif ...
);
```

---

## Design Patterns

### Pattern 1: CPU to Peripherals Bridge

Use AXI4-to-APB shim for CPU master accessing peripheral registers:

```systemverilog
// ARM Cortex-M processor → APB peripherals
axi4_to_apb_shim #(
    .AXI_ID_WIDTH(12),        // CPU master ID width
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(32),
    .APB_ADDR_WIDTH(32),
    .APB_DATA_WIDTH(32),
    .DEPTH_AW(2),             // Shallow buffers for low latency
    .DEPTH_AR(2)
) u_cpu_periph_bridge (
    .aclk(cpu_clk),
    .aresetn(cpu_resetn),
    .pclk(periph_clk),
    .presetn(periph_resetn),
    // ... connections ...
);
```

**Characteristics:**
- Low latency (shallow buffers)
- Single-beat transactions typical
- Dual-clock support

### Pattern 2: High-Speed to Low-Speed Bridge

Use width conversion for data rate adaptation:

```systemverilog
// 64-bit AXI @ 200 MHz → 32-bit APB @ 100 MHz
axi4_to_apb_shim #(
    .AXI_DATA_WIDTH(64),      // High-speed side
    .APB_DATA_WIDTH(32),      // Low-speed side (2:1)
    .DEPTH_AW(4),             // Deeper for CDC + bursts
    .DEPTH_W(8),              // Extra depth for width conversion
    .DEPTH_R(8),
    .SIDE_DEPTH(8)
) u_width_bridge (
    .aclk(axi_clk_200mhz),
    .pclk(apb_clk_100mhz),
    // ... connections ...
);
```

**Characteristics:**
- Width adaptation (automatic slicing)
- Deeper buffers for burst traffic
- Optimized for throughput

### Pattern 3: Register Block Integration

Use PeakRDL adapter for register automation:

```
APB Bus → apb_slave_stub → peakrdl_to_cmdrsp → PeakRDL Register Block
          (APB→cmd/rsp)     (cmd/rsp→cpuif)     (generated from .rdl)
```

**Benefits:**
- Register automation via PeakRDL
- Standard cmd/rsp intermediate interface
- Error propagation
- Stall handling

---

## Performance Characteristics

### AXI4 to APB Bridge

**Latency:**

| Configuration | Typical Latency | Notes |
|--------------|-----------------|-------|
| Same clock, no width convert | 5-7 cycles | Minimal overhead |
| Same clock, 2:1 width convert | 8-12 cycles | +1 cycle per APB beat |
| Dual-clock, no width convert | 12-16 cycles | +3-5 cycles per CDC |
| Dual-clock, 2:1 width convert | 15-20 cycles | Combined overhead |

**Throughput:**

| Width Ratio | Max Throughput | Notes |
|-------------|----------------|-------|
| 1:1 | 0.5 transfers/cycle | APB overhead |
| 2:1 | 0.25 transfers/cycle | Width conversion |
| 4:1 | 0.125 transfers/cycle | More APB beats |

### PeakRDL Adapter

**Latency:**
- Read: 2 cycles (no stall)
- Write: 2 cycles (no stall)
- +N cycles if PeakRDL stalls request

**Throughput:**
- Maximum: 1 transaction per 2 cycles
- Typical: 1 transaction per 3-5 cycles (with APB)

---

## Testing

```bash
# Test AXI to APB bridge
pytest val/integ_amba/test_axi2apb_shim.py -v

# Test PeakRDL adapter
pytest val/amba/test_peakrdl_to_cmdrsp.py -v

# Run all shims tests
pytest val/amba/test_*shim*.py val/integ_amba/test_*shim*.py -v

# Generate waveforms
pytest val/integ_amba/test_axi2apb_shim.py --vcd=bridge.vcd -v
gtkwave bridge.vcd
```

---

## Common Use Cases

### Use Case 1: SoC Integration

**Scenario:** ARM Cortex-M processor with AXI4 master accessing APB peripherals

**Solution:**
```systemverilog
axi4_to_apb_shim u_cpu_bridge (
    .aclk(cpu_axi_clk),
    .pclk(periph_apb_clk),
    // Connect CPU master → APB peripheral bus
);
```

**Benefits:**
- Enables CPU access to APB peripherals
- Handles clock domain crossing
- Minimal latency for register access

### Use Case 2: DMA to Peripherals

**Scenario:** DMA engine (AXI4 master) writing to APB peripheral registers

**Solution:**
```systemverilog
axi4_to_apb_shim #(
    .DEPTH_AW(8),     // Deep buffers for burst DMA
    .DEPTH_W(16)
) u_dma_bridge (
    .aclk(dma_clk),
    .pclk(periph_clk),
    // Connect DMA master → APB registers
);
```

**Benefits:**
- Burst decomposition (DMA bursts → APB single-beats)
- Deep buffering for DMA traffic
- Error reporting back to DMA

### Use Case 3: Configuration Registers

**Scenario:** Control registers for IP block, auto-generated from SystemRDL

**Solution:**
```
APB → apb_slave_stub → peakrdl_to_cmdrsp → PeakRDL config_regs
```

**Benefits:**
- Register automation (field reset, RW access, interrupts)
- Documentation generation
- Software header generation
- Type safety

---

## Parameter Selection Guidelines

### AXI to APB Bridge

**Skid Buffer Depths:**

| Application | DEPTH_AW/AR | DEPTH_W | DEPTH_R | Notes |
|-------------|-------------|---------|---------|-------|
| Low-latency CPU | 2 | 2-4 | 2-4 | Minimize latency |
| Moderate DMA | 4 | 8 | 8 | Balance latency/throughput |
| Burst DMA | 8 | 16 | 16 | Maximize throughput |

**Width Conversion:**

| AXI Width | APB Width | Ratio | Typical Use |
|-----------|-----------|-------|-------------|
| 32 | 32 | 1:1 | Simple bridging |
| 64 | 32 | 2:1 | Modern CPU → legacy periph |
| 128 | 32 | 4:1 | Wide DMA → narrow periph |
| 64 | 64 | 1:1 | High-bandwidth peripherals |

**Side FIFO Depth:**
- `SIDE_DEPTH` ≥ max(AXI burst length × width ratio)
- Typical: 4-8 for CPU, 8-16 for DMA

### PeakRDL Adapter

**Address Width:**
- Match PeakRDL generation: `--cpuif-addr-width N`
- Typical: 12 bits (4 KB register space)

**Data Width:**
- Must match PeakRDL generation (usually 32)
- No width conversion supported

---

## Design Tradeoffs

### AXI to APB Bridge

**✅ Advantages:**
- Standard protocols (AXI4 ↔ APB)
- Dual-clock CDC support
- Automatic width conversion
- Burst decomposition

**❌ Limitations:**
- APB serialization (no concurrent transactions)
- Performance overhead (APB slower than AXI)
- No AXI exclusive access support
- Resource cost (~800-1500 LUTs)

**Alternatives:**
- Native APB masters (if no AXI required)
- AXI crossbar (if staying in AXI domain)

### PeakRDL Adapter

**✅ Advantages:**
- Register automation
- Standards-based (SystemRDL)
- Documentation generation
- Low overhead (~50 LUTs)

**❌ Limitations:**
- PeakRDL dependency
- Learning curve (SystemRDL)
- 32-bit only (typical)

**Alternatives:**
- Custom register implementation
- PeakRDL native APB cpuif
- Commercial register tools

---

## Synthesis Notes

### Resource Usage

| Module | LUTs | FFs | BRAM | Notes |
|--------|------|-----|------|-------|
| axi4_to_apb_shim (32/32) | ~800 | ~600 | 0 | Minimal config |
| axi4_to_apb_shim (64/32) | ~1200 | ~900 | 0 | Width conversion |
| axi4_to_apb_convert | ~400 | ~300 | 0 | Core logic only |
| peakrdl_to_cmdrsp | ~50 | ~100 | 0 | Lightweight |

### Timing Closure

**Critical Paths:**
- AXI packet unpacking (combinatorial)
- Width conversion muxing
- CDC synchronizers

**Recommendations:**
```tcl
# Constrain CDC paths in axi4_to_apb_shim
set_false_path -from [get_clocks aclk] -to [get_clocks pclk]
set_max_delay -from */cdc_handshake/src_* -to */cdc_handshake/dst_* 10.0

# Register insertion for wide data paths
set_max_fanout 16 [get_pins */data_shift_reg*]
```

---

## Related Documentation

### Protocol Specifications

- ARM AMBA 4 AXI4 Specification
- ARM AMBA 3 APB Protocol Specification v2.0
- SystemRDL 2.0 Specification (PeakRDL)

### RTL Design Sherpa Documentation

- **[RTLAmba Overview](../overview.md)** - Complete AMBA subsystem
- **[AXI4 Modules](../axi4/README.md)** - AXI4 infrastructure
- **[APB Modules](../apb/README.md)** - APB infrastructure
- **[Shared Utilities](../shared/README.md)** - Common modules (CDC, FIFOs)

### External Resources

- **PeakRDL:** https://github.com/SystemRDL/PeakRDL
- **PeakRDL regblock:** https://github.com/SystemRDL/PeakRDL-regblock
- **PeakRDL Workflow Guide:** `rtl/amba/shims/peakrdl_adapter_README.md`

### Source Code

- RTL: `rtl/amba/shims/`
- Tests: `val/amba/test_peakrdl*.py`, `val/integ_amba/test_axi2apb*.py`
- Framework: `bin/CocoTBFramework/components/`

---

## Design Notes

### When to Use Shims

**✅ Use AXI4-to-APB Shim When:**
- Bridging AXI4 master to APB slave
- Different clock domains required
- Width conversion needed
- Burst decomposition required

**✅ Use PeakRDL Adapter When:**
- Automating register block generation
- Using SystemRDL descriptions
- Need documentation/header generation
- Integrating with cmd/rsp infrastructure

**❌ Consider Alternatives When:**
- Same protocol both sides (use crossbar)
- Need high performance (APB is slow)
- Simple registers (custom implementation may be lighter)

### Clock Domain Crossing

**AXI to APB CDC:**
- Uses `cdc_handshake` module
- Gray-code pointer-based synchronization
- Safe for arbitrary clock ratios
- Proper reset synchronization required

**Constraints Required:**
```tcl
set_false_path -from [get_clocks aclk] -to [get_clocks pclk]
set_false_path -from [get_clocks pclk] -to [get_clocks aclk]
```

---

## Migration Guide

### Upgrading from Legacy AXI-APB Bridges

**Before (legacy):**
```systemverilog
axi_apb_bridge u_bridge (
    .axi_*,  // Legacy AXI naming
    .apb_*   // Legacy APB naming
);
```

**After (RTL Design Sherpa):**
```systemverilog
axi4_to_apb_shim u_bridge (
    .s_axi_*,  // AXI slave interface
    .m_apb_*   // APB master interface
);
```

**Key Changes:**
- Explicit slave/master prefixes
- Standardized signal naming
- Added CDC support
- Parameterized buffering

---

## Troubleshooting

### Issue 1: High Latency

**Symptoms:** Slow register access, performance degradation

**Debug:**
1. Check buffer depths (DEPTH_*) - deeper = higher latency
2. Verify clock domain crossing overhead
3. Check for width conversion ratio
4. Monitor APB protocol overhead

**Solutions:**
- Reduce buffer depths for low latency
- Same-clock operation if possible
- Minimize width ratio (prefer 1:1)

### Issue 2: PeakRDL Stalls

**Symptoms:** Long delays, timeout errors

**Debug:**
1. Check `regblk_req_stall_*` signals
2. Verify PeakRDL internal logic
3. Check for field access conflicts

**Solutions:**
- Review PeakRDL register arbitration
- Check for hardware write conflicts
- Verify interrupt handling

### Issue 3: Data Corruption

**Symptoms:** Incorrect read data, write failures

**Debug:**
1. Verify width conversion logic
2. Check byte strobes (WSTRB → bit enables)
3. Monitor error signals (PSLVERR, BRESP, RRESP)

**Solutions:**
- Verify parameter configuration
- Check WSTRB alignment
- Enable error checking in testbench

---

**Last Updated:** 2025-10-20

---

## Navigation

- **[← Back to RTLAmba Index](../README.md)**
- **[← Back to Main Documentation Index](../../index.md)**
