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

# AXIS5 (AXI5-Stream) Modules

**Location:** `rtl/amba/axis5/`
**Test Location:** `val/amba/`
**Status:** Production Ready

---

## Overview

The AXIS5 subsystem provides a complete implementation of the ARM AMBA 5 AXI-Stream protocol, including masters, slaves, and clock-gated variants for high-throughput streaming data applications.

AXI5-Stream extends AXI4-Stream with enhancements for modern streaming data applications, including improved signaling for wake-up, additional user signals, and enhanced flow control mechanisms.

---

## AMBA4 vs AMBA5 Comparison

| Feature | AXI4-Stream | AXI5-Stream |
|---------|-------------|-------------|
| Basic Protocol | TVALID/TREADY handshake | TVALID/TREADY handshake |
| Wake-up | Not supported | TWAKEUP signal |
| User Signal Width | TUSER (variable) | TUSER (extended) |
| Data Poisoning | Not supported | TPOISON for error marking |
| Chunking | Not supported | TCHUNKEN for segmentation |
| Side-band Signals | TID, TDEST, TUSER | Enhanced TID, TDEST, TUSER |

---

## Module Categories

### Stream Master Components

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **axis5_master** | AXI5-Stream master for high-throughput data streaming | [axis5_master.md](axis5_master.md) | Documented |
| **axis5_master_cg** | Clock-gated AXI5-Stream master | [axis5_master_cg.md](axis5_master_cg.md) | Documented |

### Stream Slave Components

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **axis5_slave** | AXI5-Stream slave for data reception | [axis5_slave.md](axis5_slave.md) | Documented |
| **axis5_slave_cg** | Clock-gated AXI5-Stream slave | [axis5_slave_cg.md](axis5_slave_cg.md) | Documented |

---

## Key Features

### AXI5-Stream Protocol Support
- **Full AXI5-Stream Compliance:** Complete AMBA 5 streaming protocol
- **Flow Control:** TVALID/TREADY handshaking with backpressure
- **Packet Boundaries:** TLAST for packet/frame demarcation
- **Byte Qualification:** TSTRB and TKEEP for byte-level control
- **Side-band Data:** TID, TDEST, TUSER for routing and metadata

### Enhanced AXI5 Features
- **Wake-up Signaling:** TWAKEUP for low-power state exit
- **Data Poisoning:** TPOISON for error propagation in pipelines
- **Extended User Signals:** Wider TUSER for additional metadata

### Power Management
- **Clock Gating:** Per-module clock gating for power reduction
- **Wake-up Support:** TWAKEUP integration for power management
- **Idle Detection:** Automatic clock gate when stream is idle

### Performance
- **Zero-Latency Option:** Combinational pass-through mode
- **Registered Mode:** Optional pipeline stages for timing
- **Configurable Widths:** Flexible data and signal widths

---

## Quick Start

### Using AXI5-Stream Master

```systemverilog
axis5_master #(
    .SKID_DEPTH_T(4),
    .AXIS_DATA_WIDTH(128),
    .AXIS_ID_WIDTH(8),
    .AXIS_DEST_WIDTH(4),
    .AXIS_USER_WIDTH(8)
) u_axis5_master (
    .aclk               (clk),
    .aresetn            (resetn),

    // FUB streaming interface (from internal logic)
    .fub_axis_tdata     (fub_tdata),
    .fub_axis_tstrb     (fub_tstrb),
    .fub_axis_tkeep     (fub_tkeep),
    .fub_axis_tlast     (fub_tlast),
    .fub_axis_tid       (fub_tid),
    .fub_axis_tdest     (fub_tdest),
    .fub_axis_tuser     (fub_tuser),
    .fub_axis_tvalid    (fub_tvalid),
    .fub_axis_tready    (fub_tready),

    // AXI5-Stream master interface
    .m_axis_tdata       (m_tdata),
    .m_axis_tstrb       (m_tstrb),
    .m_axis_tkeep       (m_tkeep),
    .m_axis_tlast       (m_tlast),
    .m_axis_tid         (m_tid),
    .m_axis_tdest       (m_tdest),
    .m_axis_tuser       (m_tuser),
    .m_axis_twakeup     (m_twakeup),
    .m_axis_tvalid      (m_tvalid),
    .m_axis_tready      (m_tready)
);
```

### Using AXI5-Stream Slave

```systemverilog
axis5_slave #(
    .SKID_DEPTH_T(4),
    .AXIS_DATA_WIDTH(128),
    .AXIS_ID_WIDTH(8),
    .AXIS_DEST_WIDTH(4),
    .AXIS_USER_WIDTH(8)
) u_axis5_slave (
    .aclk               (clk),
    .aresetn            (resetn),

    // AXI5-Stream slave interface
    .s_axis_tdata       (s_tdata),
    .s_axis_tstrb       (s_tstrb),
    .s_axis_tkeep       (s_tkeep),
    .s_axis_tlast       (s_tlast),
    .s_axis_tid         (s_tid),
    .s_axis_tdest       (s_tdest),
    .s_axis_tuser       (s_tuser),
    .s_axis_twakeup     (s_twakeup),
    .s_axis_tvalid      (s_tvalid),
    .s_axis_tready      (s_tready),

    // FUB streaming interface (to internal logic)
    .fub_axis_tdata     (fub_tdata),
    .fub_axis_tstrb     (fub_tstrb),
    .fub_axis_tkeep     (fub_tkeep),
    .fub_axis_tlast     (fub_tlast),
    .fub_axis_tid       (fub_tid),
    .fub_axis_tdest     (fub_tdest),
    .fub_axis_tuser     (fub_tuser),
    .fub_axis_tvalid    (fub_tvalid),
    .fub_axis_tready    (fub_tready)
);
```

### Clock-Gated Streaming

```systemverilog
// Clock-gated master for power efficiency
axis5_master_cg #(
    .AXIS_DATA_WIDTH(128)
) u_axis5_master_cg (
    .aclk               (clk),
    .aresetn            (resetn),

    // Clock gating control
    .cg_enable          (stream_active),
    .cg_test_enable     (scan_test_mode),
    .gated_clk          (stream_gated_clk),

    // Streaming interfaces
    .fub_axis_*         (...),
    .m_axis_*           (...)
);
```

---

## Testing

All AXIS5 modules are verified using CocoTB-based testbenches located in `val/amba/`:

```bash
# Run all AXIS5 tests
pytest val/amba/test_axis5*.py -v

# Run specific module tests
pytest val/amba/test_axis5_master.py -v
pytest val/amba/test_axis5_slave.py -v
```

---

## Protocol Details

### AXI5-Stream Signal Descriptions

| Signal | Direction | Description |
|--------|-----------|-------------|
| ACLK | Input | Stream clock |
| ARESETn | Input | Active-low reset |
| TDATA | Master to Slave | Stream data payload |
| TSTRB | Master to Slave | Byte strobes (data vs. position) |
| TKEEP | Master to Slave | Byte qualifiers (valid bytes) |
| TLAST | Master to Slave | End of packet/frame indicator |
| TID | Master to Slave | Stream identifier |
| TDEST | Master to Slave | Destination routing information |
| TUSER | Master to Slave | User-defined sideband data |
| TWAKEUP | Master to Slave | Wake-up signal (AXI5) |
| TVALID | Master to Slave | Data valid indicator |
| TREADY | Slave to Master | Ready to accept data |

### Flow Control

AXI5-Stream uses simple valid/ready handshaking:

1. **Data Transfer:** Occurs when TVALID and TREADY are both high
2. **Backpressure:** Slave deasserts TREADY to pause stream
3. **Source Stall:** Master deasserts TVALID when no data available
4. **Packet End:** TLAST indicates final beat of packet/frame

### Byte Qualification

| TKEEP | TSTRB | Meaning |
|-------|-------|---------|
| 1 | 1 | Data byte |
| 1 | 0 | Position byte (placeholder) |
| 0 | 0 | Null byte (not transmitted) |
| 0 | 1 | Reserved |

---

## Design Notes

### FUB Interface Pattern

All AXIS5 modules use the FUB (Functional Unit Block) interface pattern:
- **fub_axis_*** signals connect to internal logic
- **m_axis_*** or **s_axis_*** signals connect to external stream bus
- Skid buffers between FUB and external interfaces for timing closure

### Migration from AXI4-Stream

AXIS5 modules are backward compatible with AXI4-Stream:
- Core protocol unchanged (TVALID/TREADY handshake)
- TWAKEUP can be tied to 0 for always-awake operation
- TUSER width can match AXI4-Stream configurations
- New signals are optional additions

### Streaming Pipeline Integration

AXIS5 modules integrate seamlessly into streaming pipelines:

```systemverilog
// Streaming data processing pipeline
axis5_master u_input (
    .m_axis_*(stage1_axis)
);

// Processing stage
processing_block u_process (
    .s_axis_*(stage1_axis),
    .m_axis_*(stage2_axis)
);

// Clock domain crossing
gaxi_fifo_async u_cdc (
    .s_*(stage2_axis),
    .m_*(stage3_axis)
);

axis5_slave u_output (
    .s_axis_*(stage3_axis)
);
```

---

## Performance Characteristics

| Metric | Typical Value |
|--------|---------------|
| Maximum Frequency | 600+ MHz |
| Latency (skid buffer) | 0-2 clock cycles |
| Throughput (128-bit, 600 MHz) | 76.8 GB/s |
| Backpressure Response | 1 clock cycle |

---

## Related Documentation

- **[AXIS4 Modules](../axis4/README.md)** - AXI4-Stream components
- **[AXI5 Modules](../axi5/README.md)** - AXI5 protocol components
- **[APB5 Modules](../apb5/README.md)** - APB5 protocol components
- **[GAXI Modules](../gaxi/README.md)** - Generic AXI utilities (FIFOs, CDC)

---

## References

### Specifications
- ARM AMBA 5 AXI-Stream Protocol Specification
- ARM AMBA AXI4-Stream Protocol Specification

### Source Code
- RTL: `rtl/amba/axis5/`
- Tests: `val/amba/test_axis5*.py`
- Framework: `bin/CocoTBFramework/components/axis4/`

---

**Last Updated:** 2025-12-26

---

## Navigation

- **[Back to RTLAmba Index](../index.md)**
- **[Back to Main Documentation Index](../../index.md)**
