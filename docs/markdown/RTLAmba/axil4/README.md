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

# AXIL4 (AXI4-Lite) Modules

**Location:** `rtl/amba/axil4/`
**Test Location:** `val/amba/`
**Status:** ✅ Production Ready

---

## Overview

The AXIL4 subsystem provides a complete implementation of the ARM AMBA AXI4-Lite protocol—a simplified subset of AXI4 designed for control register access with reduced signal count and single-beat transactions.

### Key Features

- ✅ **AXI4-Lite Protocol:** Simplified subset (no burst, no ID, no QoS)
- ✅ **Single-Beat Transactions:** Always 1 transfer per transaction
- ✅ **Reduced Signals:** 40-50% fewer signals vs full AXI4
- ✅ **Buffered Interfaces:** Elastic buffering via gaxi_skid_buffer
- ✅ **Monitoring Infrastructure:** Integrated transaction monitoring
- ✅ **Clock Gating Variants:** Power-optimized versions
- ✅ **Typical Use:** Control registers, CSRs, peripheral access

---

## Module Categories

### Core Master/Slave Modules

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|\
| **axil4_master_rd** | AXIL4 read master with buffered channels | [axil4_master_rd.md](axil4_master_rd.md) | ✅ Documented |
| **axil4_master_wr** | AXIL4 write master with buffered channels | [axil4_master_wr.md](axil4_master_wr.md) | ✅ Documented |
| **axil4_slave_rd** | AXIL4 read slave with buffered channels | [axil4_slave_rd.md](axil4_slave_rd.md) | ✅ Documented |
| **axil4_slave_wr** | AXIL4 write slave with buffered channels | [axil4_slave_wr.md](axil4_slave_wr.md) | ✅ Documented |

### Monitor Modules (Verification)

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **axil4_master_rd_mon** | Read master with integrated monitoring | [axil4_master_rd_mon.md](axil4_master_rd_mon.md) | ✅ Documented |
| **axil4_master_wr_mon** | Write master with integrated monitoring | [axil4_master_wr_mon.md](axil4_master_wr_mon.md) | ✅ Documented |
| **axil4_slave_rd_mon** | Read slave with integrated monitoring | [axil4_slave_rd_mon.md](axil4_slave_rd_mon.md) | ✅ Documented |
| **axil4_slave_wr_mon** | Write slave with integrated monitoring | [axil4_slave_wr_mon.md](axil4_slave_wr_mon.md) | ✅ Documented |

### Clock-Gated Variants

**All clock-gated variants documented in:** [axil4_clock_gating_guide.md](axil4_clock_gating_guide.md)

| Module | Base Module | Status |
|--------|-------------|--------|
| **axil4_master_rd_cg** | [axil4_master_rd](axil4_master_rd.md) | ✅ Documented |
| **axil4_master_wr_cg** | [axil4_master_wr](axil4_master_wr.md) | ✅ Documented |
| **axil4_slave_rd_cg** | [axil4_slave_rd](axil4_slave_rd.md) | ✅ Documented |
| **axil4_slave_wr_cg** | [axil4_slave_wr](axil4_slave_wr.md) | ✅ Documented |
| **axil4_master_rd_mon_cg** | [axil4_master_rd_mon](axil4_master_rd_mon.md) | ✅ Documented |
| **axil4_master_wr_mon_cg** | [axil4_master_wr_mon](axil4_master_wr_mon.md) | ✅ Documented |
| **axil4_slave_rd_mon_cg** | [axil4_slave_rd_mon](axil4_slave_rd_mon.md) | ✅ Documented |
| **axil4_slave_wr_mon_cg** | [axil4_slave_wr_mon](axil4_slave_wr_mon.md) | ✅ Documented |

---

## AXI4-Lite Protocol Overview

### Simplified vs Full AXI4

| Feature | AXI4 | AXI4-Lite |
|---------|------|-----------|
| **Burst Support** | Yes (1-256 beats) | No (always 1 beat) |
| **ID Signals** | ARID/AWID/RID/BID | None |
| **Out-of-Order** | Supported via ID | Not supported |
| **Data Width** | 8-1024 bits | 32 or 64 bits |
| **QoS/Region** | Supported | Not supported |
| **Lock/Cache** | Full support | AWLOCK/ARLOCK only |
| **Signal Count** | ~40-50 signals | ~20-25 signals |
| **Typical Use** | High-bandwidth data | Control registers |

### Channel Architecture

AXI4-Lite uses five independent channels for read and write transactions:

**Write Transaction:**
1. **AW (Write Address)** - Address and protection
2. **W (Write Data)** - Data and byte strobes
3. **B (Write Response)** - Completion status

**Read Transaction:**
1. **AR (Read Address)** - Address and protection
2. **R (Read Data)** - Data and response

### Key Signals (Simplified)

**Address Channels (AR/AW):**
- `ARADDR/AWADDR` - Byte address
- `ARPROT/AWPROT` - Protection attributes (3 bits)
- `ARVALID/AWVALID`, `ARREADY/AWREADY` - Handshake

**Data Channels (R/W):**
- `RDATA/WDATA` - Transfer data (32 or 64 bits)
- `RRESP/BRESP` - Response (OKAY, SLVERR, DECERR)
- `WSTRB` - Write strobes (byte lane enables)
- `RVALID/WVALID`, `RREADY/WREADY` - Handshake

---

## Quick Start

### Basic Read Master

```systemverilog
axil4_master_rd #(
    .AXIL_ADDR_WIDTH(32),
    .AXIL_DATA_WIDTH(32),
    .SKID_DEPTH_AR(2),    // 4 entries
    .SKID_DEPTH_R(4)      // 16 entries
) u_rd_master (
    .aclk           (axi_clk),
    .aresetn        (axi_resetn),

    // Frontend interface (from CPU)
    .fub_araddr     (cpu_araddr),
    .fub_arprot     (cpu_arprot),
    .fub_arvalid    (cpu_arvalid),
    .fub_arready    (cpu_arready),

    .fub_rdata      (cpu_rdata),
    .fub_rresp      (cpu_rresp),
    .fub_rvalid     (cpu_rvalid),
    .fub_rready     (cpu_rready),

    // Master interface (to interconnect)
    .m_axil_araddr  (periph_araddr),
    // ... rest of AR/R signals

    .busy           (rd_busy)
);
```

### Basic Write Slave

```systemverilog
axil4_slave_wr #(
    .AXIL_ADDR_WIDTH(32),
    .AXIL_DATA_WIDTH(32),
    .SKID_DEPTH_AW(2),
    .SKID_DEPTH_W(2),
    .SKID_DEPTH_B(2)
) u_wr_slave (
    .aclk             (axi_clk),
    .aresetn          (axi_resetn),

    // Slave interface (from interconnect)
    .s_axil_awaddr    (interconnect_awaddr),
    // ... rest of AW/W/B signals

    // Backend interface (to register block)
    .fub_awaddr       (regfile_awaddr),
    // ... rest of AW/W/B signals

    .busy             (wr_busy)
);
```

### Monitor Integration

```systemverilog
axil4_master_rd_mon #(
    .AXIL_ADDR_WIDTH(32),
    .AXIL_DATA_WIDTH(32),
    .UNIT_ID(1),
    .AGENT_ID(10),
    .MAX_TRANSACTIONS(8),    // Reduced for AXIL
    .ENABLE_FILTERING(1)
) u_rd_mon (
    .aclk                   (axi_clk),
    .aresetn                (axi_resetn),

    // AXIL interfaces
    .fub_axil_araddr        (cpu_araddr),
    // ... rest of AR/R signals

    // Monitor configuration
    .cfg_monitor_enable     (1'b1),
    .cfg_error_enable       (1'b1),
    .cfg_timeout_enable     (1'b1),
    .cfg_perf_enable        (1'b0),  // Avoid congestion
    .cfg_timeout_cycles     (16'd1000),

    // Filtering masks
    .cfg_axi_pkt_mask       (16'b1111_1111_0000_0011),
    // ... rest of masks

    // Monitor bus output
    .monbus_pkt_valid       (mon_valid),
    .monbus_pkt_ready       (mon_ready),
    .monbus_pkt_data        (mon_packet),

    // Status
    .busy                   (rd_busy),
    .active_transactions    (rd_active),
    .error_count            (rd_errors)
);
```

---

## Testing

All AXIL4 modules are verified using CocoTB-based testbenches:

```bash
# Run all AXIL4 tests
pytest val/amba/test_axil4*.py -v

# Run specific module tests
pytest val/amba/test_axil4_master_rd.py -v
pytest val/amba/test_axil4_slave_wr.py -v
pytest val/amba/test_axil4_master_rd_mon.py -v

# Run with waveforms
pytest val/amba/test_axil4_master_rd.py --vcd=waves.vcd -v
```

---

## Design Patterns

### Pattern 1: Buffered Master/Slave

All core modules use `gaxi_skid_buffer`:
- Decouples frontend and backend timing
- Configurable depth per channel
- 1-cycle latency overhead
- Full backpressure handling

### Pattern 2: Monitor Integration

Monitor modules combine functional core with verification:
- Uses shared **axi_monitor_filtered** (rtl/amba/shared/)
- 3-level filtering hierarchy
- 64-bit monitor bus
- Simplified for AXIL (MAX_TRANSACTIONS=8)

### Pattern 3: Clock Gating

Clock-gated variants (`*_cg`) add power management:
- Dynamic gating based on busy signal
- Test mode support
- 0-cycle ungating latency
- Better power savings than AXI4 (bursty register access)

---

## Performance Characteristics

### Throughput

| Configuration | Rate | Notes |
|--------------|------|-------|
| Single-beat read/write | 1 txn/cycle | When buffers not stalled |
| Typical peripheral | 1 txn/N cycles | N = backend response time |

### Latency

| Path | Cycles | Notes |
|------|--------|-------|
| AR → R (single) | 2-3 | Minimum read latency |
| AW+W → B (single) | 2-3 | Minimum write latency |
| Buffer overhead | +1 per channel | Skid buffer latency |

### Resource Usage

| Module Type | LUTs | FFs | BRAM | Notes |
|-------------|------|-----|------|-------|
| Master/Slave (32-bit) | ~200 | ~150 | 0 | Per direction (rd/wr) |
| Monitor (+mon) | +800 | +600 | 0 | Additional overhead |
| Clock-gated (+cg) | +50 | +30 | 0 | Clock gating logic |

**vs AXI4:** ~40-50% resource savings (no ID tracking, no burst, simpler protocol)

---

## Related Documentation

### Protocol Specifications
- ARM IHI 0022E: AMBA AXI Protocol Specification
- Chapter 4: AXI4-Lite

### RTL Design Sherpa Documentation
- **[RTLAmba Overview](../overview.md)** - Complete AMBA subsystem architecture
- **[AXI4 Modules](../axi4/README.md)** - Full AXI4 protocol (comparison)
- **[APB Modules](../apb/README.md)** - Even simpler peripheral bus
- **[GAXI Modules](../gaxi/README.md)** - Generic AXI utilities (buffers, FIFOs)

### Configuration and Integration
- **[AXI Monitor Configuration Guide](../shared/axi_monitor_base.md)** - Monitor setup strategies
- **[Monitor Packet Specification](../includes/monitor_package_spec.md)** - 64-bit packet format

### Source Code
- RTL: `rtl/amba/axil4/`
- Tests: `val/amba/test_axil4*.py`
- Framework: `bin/CocoTBFramework/components/axil4/`
- Shared Infrastructure: `rtl/amba/shared/` (monitor base, gaxi_skid_buffer)

---

## Design Notes

### When to Use AXI4-Lite

**✅ Use AXI4-Lite For:**
- Control and status registers (CSRs)
- Peripheral configuration interfaces
- Low-bandwidth control paths
- Resource-constrained designs
- Simpler protocol requirements

**❌ Use Full AXI4 For:**
- High-bandwidth data transfers
- Burst transactions required
- Out-of-order support needed
- DMA engines, memory controllers
- Streaming data

### Buffer Depth Guidelines

**Address Channels (AR/AW):**
- Default: 2 (4 entries) - sufficient for most register access
- Increase for high-latency address decode

**Data Channels (R/W):**
- Default: 4 (16 entries) for R, 2 (4 entries) for W
- R channel typically deeper (accommodate backend latency)
- W channel can be shallower (single-beat)

**Response Channel (B):**
- Default: 2 (4 entries) - responses are single-beat
- Rarely needs adjustment

---

**Last Updated:** 2025-10-20

---

## Navigation

- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
