# AXI4 (Advanced eXtensible Interface) Modules

**Location:** `rtl/amba/axi4/`
**Test Location:** `val/amba/`
**Status:** ✅ Production Ready

---

## Overview

The AXI4 subsystem provides a complete implementation of the ARM AMBA AXI4 protocol, including masters, slaves, monitors, data width converters, and interconnect components. AXI4 is a high-performance, high-frequency protocol designed for multi-master, multi-slave systems with out-of-order transaction support.

### Key Features

- ✅ **Full AXI4 Protocol Support:** Complete implementation of read and write channels
- ✅ **Burst Transactions:** Support for fixed, incrementing, and wrapping bursts
- ✅ **Out-of-Order Support:** ID-based transaction tracking and completion
- ✅ **Quality of Service (QoS):** Priority-based arbitration support
- ✅ **Monitoring Infrastructure:** Comprehensive verification and debug capabilities
- ✅ **Data Width Conversion:** Automatic upsizing and downsizing
- ✅ **Clock Gating Variants:** Power-optimized versions with dynamic gating

---

## Module Categories

### Core Master/Slave Modules

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **axi4_master_rd** | AXI4 read master with buffered channels | [axi4_master_rd.md](axi4_master_rd.md) | ✅ Documented |
| **axi4_master_wr** | AXI4 write master with buffered channels | [axi4_master_wr.md](axi4_master_wr.md) | ✅ Documented |
| **axi4_slave_rd** | AXI4 read slave with buffered channels | [axi4_slave_rd.md](axi4_slave_rd.md) | ✅ Documented |
| **axi4_slave_wr** | AXI4 write slave with buffered channels | [axi4_slave_wr.md](axi4_slave_wr.md) | ✅ Documented |

### Monitor Modules (Verification)

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **axi4_master_rd_mon** | Read master with integrated monitoring | [axi4_master_rd_mon.md](axi4_master_rd_mon.md) | ✅ Documented |
| **axi4_master_wr_mon** | Write master with integrated monitoring | [axi4_master_wr_mon.md](axi4_master_wr_mon.md) | ✅ Documented |
| **axi4_slave_rd_mon** | Read slave with integrated monitoring | [axi4_slave_rd_mon.md](axi4_slave_rd_mon.md) | ✅ Documented |
| **axi4_slave_wr_mon** | Write slave with integrated monitoring | [axi4_slave_wr_mon.md](axi4_slave_wr_mon.md) | ✅ Documented |

### Data Width Converters

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **axi4_dwidth_converter** | Bidirectional data width conversion | [axi4_dwidth_converter.md](axi4_dwidth_converter.md) | ✅ Documented |
| **axi4_dwidth_converter_rd** | Read-only data width conversion | [axi4_dwidth_converter_rd.md](axi4_dwidth_converter_rd.md) | ✅ Documented |
| **axi4_dwidth_converter_wr** | Write-only data width conversion | [axi4_dwidth_converter_wr.md](axi4_dwidth_converter_wr.md) | ✅ Documented |

### Interconnect

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **axi4_interconnect_2x2_mon** | 2x2 AXI4 crossbar with monitoring | [axi4_interconnect_2x2_mon.md](axi4_interconnect_2x2_mon.md) | ✅ Documented |

### Clock-Gated Variants

**All clock-gated variants documented in:** [axi4_clock_gating_guide.md](axi4_clock_gating_guide.md)

| Module | Base Module | Status |
|--------|-------------|--------|
| **axi4_master_rd_cg** | [axi4_master_rd](axi4_master_rd.md) | ✅ Documented |
| **axi4_master_wr_cg** | [axi4_master_wr](axi4_master_wr.md) | ✅ Documented |
| **axi4_slave_rd_cg** | [axi4_slave_rd](axi4_slave_rd.md) | ✅ Documented |
| **axi4_slave_wr_cg** | [axi4_slave_wr](axi4_slave_wr.md) | ✅ Documented |
| **axi4_master_rd_mon_cg** | [axi4_master_rd_mon](axi4_master_rd_mon.md) | ✅ Documented |
| **axi4_master_wr_mon_cg** | [axi4_master_wr_mon](axi4_master_wr_mon.md) | ✅ Documented |
| **axi4_slave_rd_mon_cg** | [axi4_slave_rd_mon](axi4_slave_rd_mon.md) | ✅ Documented |
| **axi4_slave_wr_mon_cg** | [axi4_slave_wr_mon](axi4_slave_wr_mon.md) | ✅ Documented |

---

## AXI4 Protocol Overview

### Channel Architecture

AXI4 uses five independent channels for read and write transactions:

**Write Transaction:**
1. **AW (Write Address)** - Master → Slave: Address and control
2. **W (Write Data)** - Master → Slave: Data and strobes
3. **B (Write Response)** - Slave → Master: Completion status

**Read Transaction:**
1. **AR (Read Address)** - Master → Slave: Address and control
2. **R (Read Data)** - Slave → Master: Data and response

### Key Signals

**Address Channels (AR/AW):**
- `ARID/AWID` - Transaction ID for reordering
- `ARADDR/AWADDR` - Byte address
- `ARLEN/AWLEN` - Burst length (1-256 beats)
- `ARSIZE/AWSIZE` - Transfer size (1, 2, 4, 8, 16, ... 128 bytes)
- `ARBURST/AWBURST` - Burst type (FIXED, INCR, WRAP)
- `ARCACHE/AWCACHE` - Cache attributes
- `ARPROT/AWPROT` - Protection attributes
- `ARQOS/AWQOS` - Quality of Service

**Data Channels (R/W):**
- `RID/WID` - Transaction ID (RID only in AXI4)
- `RDATA/WDATA` - Transfer data
- `RRESP/BRESP` - Response (OKAY, EXOKAY, SLVERR, DECERR)
- `RLAST/WLAST` - Last transfer in burst
- `WSTRB` - Write strobes (byte lane enables)

---

## Quick Start

### Basic Read Master

```systemverilog
axi4_master_rd #(
    .SKID_DEPTH_AR(2),
    .SKID_DEPTH_R(4),
    .AXI_ID_WIDTH(4),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64)
) u_rd_master (
    .aclk           (axi_clk),
    .aresetn        (axi_resetn),

    // Frontend interface
    .fub_axi_arid     (cpu_arid),
    .fub_axi_araddr   (cpu_araddr),
    .fub_axi_arlen    (cpu_arlen),
    // ... rest of AR/R signals

    // Master interface
    .m_axi_arid       (m_axi_arid),
    .m_axi_araddr     (m_axi_araddr),
    // ... rest of AR/R signals

    .busy             (rd_busy)
);
```

### Basic Write Slave

```systemverilog
axi4_slave_wr #(
    .SKID_DEPTH_AW(2),
    .SKID_DEPTH_W(4),
    .SKID_DEPTH_B(2),
    .AXI_ID_WIDTH(4),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64)
) u_wr_slave (
    .aclk             (axi_clk),
    .aresetn          (axi_resetn),

    // Slave interface (from interconnect)
    .s_axi_awid       (s_axi_awid),
    .s_axi_awaddr     (s_axi_awaddr),
    // ... rest of AW/W/B signals

    // Backend interface (to memory/logic)
    .fub_axi_awid     (mem_awid),
    .fub_axi_awaddr   (mem_awaddr),
    // ... rest of AW/W/B signals

    .busy             (wr_busy)
);
```

### Monitor Integration

```systemverilog
axi4_master_rd_mon #(
    .SKID_DEPTH_AR(2),
    .SKID_DEPTH_R(4),
    .AXI_ID_WIDTH(4),
    .AXI_ADDR_WIDTH(32),
    .AXI_DATA_WIDTH(64),
    .UNIT_ID(1),
    .AGENT_ID(10),
    .MAX_TRANSACTIONS(16),
    .ENABLE_FILTERING(1)
) u_rd_mon (
    .aclk               (axi_clk),
    .aresetn            (axi_resetn),

    // AXI interfaces
    .fub_axi_*(frontend_axi_*),
    .m_axi_*(master_axi_*),

    // Monitor configuration
    .cfg_monitor_enable     (1'b1),
    .cfg_error_enable       (1'b1),
    .cfg_timeout_enable     (1'b1),
    .cfg_perf_enable        (1'b0),
    .cfg_timeout_cycles     (16'd1000),

    // Filtering configuration
    .cfg_axi_pkt_mask       (16'b1111_1111_0000_0011),
    .cfg_axi_error_mask     (16'h0000),
    // ... rest of mask signals

    // Monitor bus output
    .monbus_valid           (mon_valid),
    .monbus_ready           (mon_ready),
    .monbus_packet          (mon_packet),

    // Status
    .busy                   (rd_busy),
    .active_transactions    (rd_active),
    .error_count            (rd_errors)
);
```

---

## Testing

All AXI4 modules are verified using CocoTB-based testbenches:

```bash
# Run all AXI4 tests
pytest val/amba/test_axi4*.py -v

# Run specific module tests
pytest val/amba/test_axi4_master_rd.py -v
pytest val/amba/test_axi4_slave_wr.py -v
pytest val/amba/test_axi4_master_rd_mon.py -v

# Run data width converter tests
pytest val/amba/test_axi4_dwidth_converter*.py -v

# Run with waveforms
pytest val/amba/test_axi4_master_rd.py --vcd=waves.vcd -v
```

---

## Design Patterns

### Pattern 1: Buffered Master/Slave

All core modules use `gaxi_skid_buffer` for elastic buffering:
- Decouples frontend and backend timing
- Configurable depth per channel
- Minimal latency overhead (1 cycle)
- Full backpressure handling

### Pattern 2: Monitor Integration

Monitor modules combine functional core with verification:
- Non-invasive monitoring (tap signals)
- 3-level filtering hierarchy
- 64-bit standardized monitor bus
- Real-time error detection

### Pattern 3: Clock Gating

Clock-gated variants (`*_cg`) add power management:
- Dynamic clock gating based on busy signal
- Test mode support for scan insertion
- Minimal area overhead

---

## Performance Characteristics

### Throughput

| Configuration | Address CH | Data CH | Notes |
|--------------|------------|---------|-------|
| Single transaction | 1 txn/cycle | 1 beat/cycle | When buffers not stalled |
| Burst (len=16) | 1 txn/16 cycles | 1 beat/cycle | Sustained |
| Multiple outstanding | Up to MAX_TRANS | 1 beat/cycle | Out-of-order |

### Latency

| Path | Cycles | Notes |
|------|--------|-------|
| AR → R (single) | 2-3 | Minimum read latency |
| AW → B (single) | 2-3 | Minimum write latency |
| Buffer overhead | +1 per channel | Skid buffer latency |

### Resource Usage

| Module Type | LUTs | FFs | BRAM | Notes |
|-------------|------|-----|------|-------|
| Master/Slave (32-bit) | ~500 | ~600 | 0 | Per direction (rd/wr) |
| Monitor (+mon) | +1000 | +800 | 0 | Additional overhead |
| Clock-gated (+cg) | +50 | +30 | 0 | Clock gating logic |

---

## Related Documentation

### Protocol Specifications
- ARM IHI 0022E: AMBA AXI Protocol Specification (AXI4)
- ARM IHI 0022D: AMBA AXI and ACE Protocol Specification (AXI3/AXI4/AXI5)

### RTL Design Sherpa Documentation
- **[RTLAmba Overview](../overview.md)** - Complete AMBA subsystem architecture
- **[APB Modules](../apb/README.md)** - Advanced Peripheral Bus
- **[AXIL4 Modules](../axil4/README.md)** - AXI4-Lite (simplified protocol)
- **[AXIS4 Modules](../axis4/README.md)** - AXI4-Stream (streaming data)
- **[GAXI Modules](../gaxi/README.md)** - Generic AXI utilities (buffers, FIFOs)

### Configuration and Integration
- **[AXI Monitor Configuration Guide](../../AXI_Monitor_Configuration_Guide.md)** - Monitor setup strategies
- **[Monitor Packet Specification](../includes/monitor_package_spec.md)** - 64-bit packet format

### Source Code
- RTL: `rtl/amba/axi4/`
- Tests: `val/amba/test_axi4*.py`
- Framework: `bin/CocoTBFramework/components/axi4/`
- Shared Infrastructure: `rtl/amba/shared/` (monitor base, transaction manager)

---

## Design Notes

### ID Width Selection

Choose ID width based on system requirements:
- **4 bits (16 IDs):** Single master systems, simple slaves
- **8 bits (256 IDs):** Multi-master systems, reordering support
- **12+ bits:** Large systems, extensive out-of-order capability

### Buffer Depth Guidelines

**Address Channels (AR/AW):**
- Default: 2 (4 entries) - sufficient for most cases
- Increase for high-latency address decode or frequent backpressure

**Data Channels (R/W):**
- Default: 4 (16 entries) - accommodates moderate bursts
- Increase for large bursts (AWLEN/ARLEN > 8)
- Deep buffers for variable latency backends

**Response Channel (B):**
- Default: 2 (4 entries) - responses are single-beat
- Increase for many concurrent outstanding writes

### Burst Optimization

Optimize burst parameters for efficiency:
```systemverilog
// Cache line burst (64 bytes, 8x 64-bit)
.ARLEN    = 8'd7,          // 8 beats
.ARSIZE   = 3'b011,        // 8 bytes per beat
.ARBURST  = 2'b01          // INCR
```

---

**Last Updated:** 2025-10-20

---

## Navigation

- **[← Back to RTLAmba Index](../README.md)**
- **[← Back to Main Documentation Index](../../index.md)**
