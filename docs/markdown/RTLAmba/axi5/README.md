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

# AXI5 (Advanced eXtensible Interface - AMBA 5) Modules

**Location:** `rtl/amba/axi5/`
**Test Location:** `val/amba/`
**Status:** Production Ready

---

## Overview

The AXI5 subsystem provides a comprehensive implementation of the ARM AMBA 5 AXI (Advanced eXtensible Interface) protocol, including read/write masters and slaves, integrated monitors, clock-gated variants, and combined master+monitor modules for efficient system integration.

AXI5 extends AXI4 with significant enhancements for modern high-performance SoC designs, including atomic operations, quality of service improvements, memory tagging, and enhanced coherency support.

---

## AMBA4 vs AMBA5 Comparison

| Feature | AXI4 | AXI5 |
|---------|------|------|
| Outstanding Transactions | Up to 16 | Up to 256 |
| Atomic Operations | Not supported | AtomicStore, AtomicLoad, AtomicSwap, AtomicCompare |
| Memory Tagging | Not supported | AWMEMATTR, ARMEMATTR |
| Cache Maintenance | Limited | Enhanced CMO support |
| QoS | ARQOS/AWQOS | Enhanced QoS with ARQOSACCEPT/AWQOSACCEPT |
| User Signals | ARUSER/AWUSER/etc. | Extended user signal widths |
| Chunking | Not supported | AWCHUNKEN for large transfers |
| Loop Support | Not supported | AWLOOP, ARLOOP for DMA |
| Poison | Not supported | RPOISON, WPOISON for error propagation |

---

## Module Categories

### Master Components

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **axi5_master_rd** | AXI5 read master with skid buffers and burst support | [axi5_master_rd.md](axi5_master_rd.md) | Documented |
| **axi5_master_rd_cg** | Clock-gated AXI5 read master | [axi5_master_rd_cg.md](axi5_master_rd_cg.md) | Documented |
| **axi5_master_wr** | AXI5 write master with address/data coordination | [axi5_master_wr.md](axi5_master_wr.md) | Documented |
| **axi5_master_wr_cg** | Clock-gated AXI5 write master | [axi5_master_wr_cg.md](axi5_master_wr_cg.md) | Documented |

### Slave Components

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **axi5_slave_rd** | AXI5 read slave with configurable response handling | [axi5_slave_rd.md](axi5_slave_rd.md) | Documented |
| **axi5_slave_rd_cg** | Clock-gated AXI5 read slave | [axi5_slave_rd_cg.md](axi5_slave_rd_cg.md) | Documented |
| **axi5_slave_wr** | AXI5 write slave with write response generation | [axi5_slave_wr.md](axi5_slave_wr.md) | Documented |
| **axi5_slave_wr_cg** | Clock-gated AXI5 write slave | [axi5_slave_wr_cg.md](axi5_slave_wr_cg.md) | Documented |

### Monitor Components

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **axi5_master_rd_mon** | AXI5 read master with integrated transaction monitor | [axi5_master_rd_mon.md](axi5_master_rd_mon.md) | Documented |
| **axi5_master_rd_mon_cg** | Clock-gated read master with monitor | [axi5_master_rd_mon_cg.md](axi5_master_rd_mon_cg.md) | Documented |
| **axi5_master_wr_mon** | AXI5 write master with integrated transaction monitor | [axi5_master_wr_mon.md](axi5_master_wr_mon.md) | Documented |
| **axi5_master_wr_mon_cg** | Clock-gated write master with monitor | [axi5_master_wr_mon_cg.md](axi5_master_wr_mon_cg.md) | Documented |
| **axi5_slave_rd_mon** | AXI5 read slave with integrated transaction monitor | [axi5_slave_rd_mon.md](axi5_slave_rd_mon.md) | Documented |
| **axi5_slave_rd_mon_cg** | Clock-gated read slave with monitor | [axi5_slave_rd_mon_cg.md](axi5_slave_rd_mon_cg.md) | Documented |
| **axi5_slave_wr_mon** | AXI5 write slave with integrated transaction monitor | [axi5_slave_wr_mon.md](axi5_slave_wr_mon.md) | Documented |
| **axi5_slave_wr_mon_cg** | Clock-gated write slave with monitor | [axi5_slave_wr_mon_cg.md](axi5_slave_wr_mon_cg.md) | Documented |

---

## Key Features

### AXI5 Protocol Support
- **Full AXI5 Compliance:** Complete AMBA 5 AXI protocol implementation
- **Burst Support:** INCR, FIXED, and WRAP burst types
- **Outstanding Transactions:** Up to 256 concurrent transactions
- **ID Reordering:** Full transaction ID support with reordering
- **Atomic Operations:** AtomicStore, AtomicLoad, AtomicSwap, AtomicCompare

### Advanced Features
- **Memory Tagging:** AWMEMATTR/ARMEMATTR for memory type attributes
- **QoS Enhancement:** Extended quality of service signaling
- **Poison Support:** RPOISON/WPOISON for error propagation
- **Chunking:** AWCHUNKEN for efficient large transfers
- **Loop Operations:** AWLOOP/ARLOOP for DMA acceleration

### Power Management
- **Clock Gating:** Per-module clock gating for power reduction
- **Idle Detection:** Automatic clock gate when interface is idle
- **Low-Power Modes:** Support for system low-power state integration

### Monitoring and Debug
- **Integrated Monitors:** Combined master/slave + monitor modules
- **Transaction Tracking:** Complete transaction lifecycle monitoring
- **Performance Metrics:** Bandwidth, latency, and utilization
- **64-bit Monitor Bus:** Standardized packet format

---

## Quick Start

### Using AXI5 Read Master

```systemverilog
axi5_master_rd #(
    .SKID_DEPTH_AR(2),
    .SKID_DEPTH_R(4),
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(64),
    .AXI_DATA_WIDTH(128),
    .AXI_USER_WIDTH(4)
) u_axi5_rd_master (
    .aclk               (clk),
    .aresetn            (resetn),

    // FUB (Functional Unit Block) interface
    .fub_axi_arid       (fub_arid),
    .fub_axi_araddr     (fub_araddr),
    .fub_axi_arlen      (fub_arlen),
    .fub_axi_arsize     (fub_arsize),
    .fub_axi_arburst    (fub_arburst),
    .fub_axi_arlock     (fub_arlock),
    .fub_axi_arcache    (fub_arcache),
    .fub_axi_arprot     (fub_arprot),
    .fub_axi_arqos      (fub_arqos),
    .fub_axi_arregion   (fub_arregion),
    .fub_axi_aruser     (fub_aruser),
    .fub_axi_arvalid    (fub_arvalid),
    .fub_axi_arready    (fub_arready),

    .fub_axi_rid        (fub_rid),
    .fub_axi_rdata      (fub_rdata),
    .fub_axi_rresp      (fub_rresp),
    .fub_axi_rlast      (fub_rlast),
    .fub_axi_ruser      (fub_ruser),
    .fub_axi_rvalid     (fub_rvalid),
    .fub_axi_rready     (fub_rready),

    // AXI5 master interface
    .m_axi_ar*          (mem_ar*),
    .m_axi_r*           (mem_r*)
);
```

### Using AXI5 Write Master

```systemverilog
axi5_master_wr #(
    .SKID_DEPTH_AW(2),
    .SKID_DEPTH_W(4),
    .SKID_DEPTH_B(2),
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(64),
    .AXI_DATA_WIDTH(128),
    .AXI_USER_WIDTH(4)
) u_axi5_wr_master (
    .aclk               (clk),
    .aresetn            (resetn),

    // FUB interface
    .fub_axi_awid       (fub_awid),
    .fub_axi_awaddr     (fub_awaddr),
    .fub_axi_awlen      (fub_awlen),
    .fub_axi_awsize     (fub_awsize),
    .fub_axi_awburst    (fub_awburst),
    .fub_axi_awlock     (fub_awlock),
    .fub_axi_awcache    (fub_awcache),
    .fub_axi_awprot     (fub_awprot),
    .fub_axi_awqos      (fub_awqos),
    .fub_axi_awregion   (fub_awregion),
    .fub_axi_awuser     (fub_awuser),
    .fub_axi_awvalid    (fub_awvalid),
    .fub_axi_awready    (fub_awready),

    .fub_axi_wdata      (fub_wdata),
    .fub_axi_wstrb      (fub_wstrb),
    .fub_axi_wlast      (fub_wlast),
    .fub_axi_wuser      (fub_wuser),
    .fub_axi_wvalid     (fub_wvalid),
    .fub_axi_wready     (fub_wready),

    .fub_axi_bid        (fub_bid),
    .fub_axi_bresp      (fub_bresp),
    .fub_axi_buser      (fub_buser),
    .fub_axi_bvalid     (fub_bvalid),
    .fub_axi_bready     (fub_bready),

    // AXI5 master interface
    .m_axi_aw*          (mem_aw*),
    .m_axi_w*           (mem_w*),
    .m_axi_b*           (mem_b*)
);
```

### Using Integrated Monitor Modules

```systemverilog
// AXI5 master with built-in transaction monitoring
axi5_master_rd_mon #(
    .AXI_ID_WIDTH(8),
    .AXI_ADDR_WIDTH(64),
    .AXI_DATA_WIDTH(128)
) u_axi5_rd_master_mon (
    .aclk               (clk),
    .aresetn            (resetn),

    // FUB and AXI interfaces (same as non-monitor version)
    .fub_axi_ar*        (...),
    .fub_axi_r*         (...),
    .m_axi_ar*          (...),
    .m_axi_r*           (...),

    // Monitor bus output
    .mon_valid          (rd_mon_valid),
    .mon_ready          (rd_mon_ready),
    .mon_data           (rd_mon_data)
);
```

---

## Testing

All AXI5 modules are verified using CocoTB-based testbenches located in `val/amba/`:

```bash
# Run all AXI5 tests
pytest val/amba/test_axi5*.py -v

# Run specific module tests
pytest val/amba/test_axi5_master_rd.py -v
pytest val/amba/test_axi5_master_wr.py -v
pytest val/amba/test_axi5_slave_rd.py -v
pytest val/amba/test_axi5_slave_wr.py -v
```

---

## Protocol Details

### AXI5 Channel Overview

AXI5 maintains the five-channel architecture from AXI4:

| Channel | Direction | Purpose |
|---------|-----------|---------|
| AR (Address Read) | Master to Slave | Read address and control |
| R (Read Data) | Slave to Master | Read data and response |
| AW (Address Write) | Master to Slave | Write address and control |
| W (Write Data) | Master to Slave | Write data |
| B (Write Response) | Slave to Master | Write response |

### AXI5 Enhanced Signals

| Signal | Channel | Description |
|--------|---------|-------------|
| AWATOP | AW | Atomic operation type |
| AWMEMATTR | AW | Memory attributes for tagging |
| ARMEMATTR | AR | Memory attributes for tagging |
| AWCHUNKEN | AW | Chunking enable for large transfers |
| AWLOOP | AW | Loop iteration count |
| ARLOOP | AR | Loop iteration count |
| RPOISON | R | Data poisoned indicator |
| WPOISON | W | Write data poisoned indicator |
| AWQOSACCEPT | B | QoS acceptance indicator |
| ARQOSACCEPT | R | QoS acceptance indicator |

### Burst Types

| ARBURST/AWBURST | Type | Description |
|-----------------|------|-------------|
| 2'b00 | FIXED | Fixed address for FIFO access |
| 2'b01 | INCR | Incrementing address burst |
| 2'b10 | WRAP | Wrapping burst for cache line |
| 2'b11 | Reserved | Not used |

---

## Design Notes

### FUB Interface Pattern

All AXI5 modules use the FUB (Functional Unit Block) interface pattern:
- **fub_axi_*** signals connect to internal logic
- **m_axi_*** or **s_axi_*** signals connect to external AXI bus
- Skid buffers between FUB and external interfaces for timing closure

### Migration from AXI4

AXI5 modules are backward compatible with AXI4:
- Core protocol unchanged (5-channel architecture)
- New signals can be tied to default values
- AWATOP tied to 0 disables atomic operations
- AWMEMATTR/ARMEMATTR can use default values
- User signal widths can match AXI4 configurations

### Monitor Integration

The `*_mon` variants combine master/slave with integrated monitor:
- Single instantiation for both data path and monitoring
- Shared clock and reset
- Monitor bus output for transaction visibility
- Reduced resource usage vs. separate monitor instantiation

---

## Performance Characteristics

| Metric | Typical Value |
|--------|---------------|
| Maximum Frequency | 500+ MHz |
| Latency (simple transaction) | 1-2 clock cycles |
| Throughput (128-bit, 500 MHz) | 64 GB/s per direction |
| Outstanding Transactions | Up to 256 |

---

## Related Documentation

- **[AXI4 Modules](../axi4/README.md)** - AXI4 protocol components
- **[APB5 Modules](../apb5/README.md)** - APB5 protocol components
- **[AXIS5 Modules](../axis5/README.md)** - AXI5-Stream components
- **[GAXI Modules](../gaxi/README.md)** - Generic AXI utilities
- **[Shared Infrastructure](../shared/README.md)** - Common components

---

## References

### Specifications
- ARM AMBA 5 AXI Protocol Specification
- ARM AMBA AXI and ACE Protocol Specification (AXI4)

### Source Code
- RTL: `rtl/amba/axi5/`
- Tests: `val/amba/test_axi5*.py`
- Framework: `bin/CocoTBFramework/components/axi4/`

---

**Last Updated:** 2025-12-26

---

## Navigation

- **[Back to RTLAmba Index](../index.md)**
- **[Back to Main Documentation Index](../../index.md)**
