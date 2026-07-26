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

The AXIS5 subsystem provides AXI5-Stream master and slave endpoints, plus clock-gated variants, for high-throughput streaming data applications.

AXI5-Stream extends AXI4-Stream primarily with wake-up signalling (TWAKEUP) for low-power operation. These modules implement the AXI4-Stream handshake and signal set, add TWAKEUP, and add an optional per-byte data parity sideband (TPARITY) that is an RTL Design Sherpa extension, not an ARM signal.

---

## Implemented Signal Set

Read this table before integrating with third-party AXI-Stream IP. It is the authoritative statement of what the RTL in `rtl/amba/axis5/` actually carries.

| Signal | Status in these modules | Notes |
|--------|-------------------------|-------|
| TDATA | Implemented | Width set by `AXIS_DATA_WIDTH` |
| TSTRB | Implemented | Width `AXIS_DATA_WIDTH/8` |
| TKEEP | **Not implemented** | No TKEEP port exists. See "Byte Qualification" below |
| TLAST | Implemented | Packet/frame boundary |
| TID | Implemented | Width `AXIS_ID_WIDTH` (default 8, set 0 to remove) |
| TDEST | Implemented | Width `AXIS_DEST_WIDTH` (default 4, set 0 to remove) |
| TUSER | Implemented | Width `AXIS_USER_WIDTH` (default 1, set 0 to remove) |
| TVALID / TREADY | Implemented | Standard handshake |
| TWAKEUP | Implemented, optional | Gated by `ENABLE_WAKEUP` (default 1) |
| TPARITY | Implemented, optional | **Not an ARM signal** - RTL Design Sherpa extension, gated by `ENABLE_PARITY` (default 0) |

**Deviations from the ARM AXI-Stream signal set:**

- **No TKEEP.** These modules carry TSTRB only. Null bytes (the TKEEP=0 encoding) cannot be expressed. A stream that needs null-byte signalling must carry that information in TUSER or use a different endpoint.
- **TPARITY is proprietary.** It occupies no ARM-defined signal name and will not connect to third-party AXI5-Stream IP. Leave `ENABLE_PARITY=0` (the default) for interoperable designs.
- **No TPOISON and no chunking (TCHUNKEN) support.** Neither signal is present in the RTL.
- **TID default width is 8 bits.** `AXIS_ID_WIDTH` is a free parameter, so wider IDs are configurable, but nothing in these modules requires or defaults to a wider ID.

---

## AXIS4 vs AXIS5 in This Library

This table compares the two generations *as implemented here*, not the full ARM specifications.

| Feature | AXIS4 modules (`rtl/amba/axis4/`) | AXIS5 modules (`rtl/amba/axis5/`) |
|---------|-----------------------------------|-----------------------------------|
| Basic protocol | TVALID/TREADY handshake | TVALID/TREADY handshake |
| Wake-up | Not present | TWAKEUP, gated by `ENABLE_WAKEUP` |
| Data parity | Not present | TPARITY sideband plus sticky `parity_error`, gated by `ENABLE_PARITY` (proprietary extension) |
| Side-band signals | TID, TDEST, TUSER | TID, TDEST, TUSER (same, parameterized widths) |
| Byte qualification | TSTRB only | TSTRB only |
| Clock gating | Available (`_cg` variants) | Available (`_cg` variants) |

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
- **Flow Control:** TVALID/TREADY handshaking with backpressure
- **Packet Boundaries:** TLAST for packet/frame demarcation
- **Byte Qualification:** TSTRB (TKEEP is not implemented - see "Implemented Signal Set")
- **Side-band Data:** TID, TDEST, TUSER for routing and metadata

### AXI5 and Extension Features
- **Wake-up Signaling:** TWAKEUP for low-power state exit
- **Optional Data Parity:** TPARITY, one bit per byte, with a sticky `parity_error` flag (proprietary extension)
- **Parameterized Side-band Widths:** TID, TDEST, and TUSER widths are set per instance

### Power Management
- **Clock Gating:** Per-module clock gating for power reduction
- **Wake-up Support:** TWAKEUP integration for power management
- **Idle Detection:** Automatic clock gate when stream is idle

### Performance
- **Skid-Buffered Path:** All four modules pass data through a `gaxi_skid_buffer`; there is no combinational bypass mode
- **Full-Rate Streaming:** One transfer per clock sustained when downstream keeps TREADY asserted
- **Configurable Widths:** Flexible data and signal widths

---

## Quick Start

### Using AXI5-Stream Master

```systemverilog
axis5_master #(
    .SKID_DEPTH         (4),
    .AXIS_DATA_WIDTH    (128),
    .AXIS_ID_WIDTH      (8),
    .AXIS_DEST_WIDTH    (4),
    .AXIS_USER_WIDTH    (8),
    .ENABLE_WAKEUP      (1),
    .ENABLE_PARITY      (0)
) u_axis5_master (
    .aclk               (clk),
    .aresetn            (resetn),

    // FUB streaming interface (from internal logic)
    .fub_axis_tdata     (fub_tdata),
    .fub_axis_tstrb     (fub_tstrb),
    .fub_axis_tlast     (fub_tlast),
    .fub_axis_tid       (fub_tid),
    .fub_axis_tdest     (fub_tdest),
    .fub_axis_tuser     (fub_tuser),
    .fub_axis_tvalid    (fub_tvalid),
    .fub_axis_tready    (fub_tready),
    .fub_axis_twakeup   (fub_twakeup),
    .fub_axis_tparity   ('0),            // Unused when ENABLE_PARITY=0

    // AXI5-Stream master interface
    .m_axis_tdata       (m_tdata),
    .m_axis_tstrb       (m_tstrb),
    .m_axis_tlast       (m_tlast),
    .m_axis_tid         (m_tid),
    .m_axis_tdest       (m_tdest),
    .m_axis_tuser       (m_tuser),
    .m_axis_tvalid      (m_tvalid),
    .m_axis_tready      (m_tready),
    .m_axis_twakeup     (m_twakeup),
    .m_axis_tparity     (),              // Unused when ENABLE_PARITY=0

    // Status
    .busy               (m_busy),
    .parity_error       ()               // Unused when ENABLE_PARITY=0
);
```

### Using AXI5-Stream Slave

```systemverilog
axis5_slave #(
    .SKID_DEPTH         (4),
    .AXIS_DATA_WIDTH    (128),
    .AXIS_ID_WIDTH      (8),
    .AXIS_DEST_WIDTH    (4),
    .AXIS_USER_WIDTH    (8),
    .ENABLE_WAKEUP      (1),
    .ENABLE_PARITY      (0)
) u_axis5_slave (
    .aclk               (clk),
    .aresetn            (resetn),

    // AXI5-Stream slave interface
    .s_axis_tdata       (s_tdata),
    .s_axis_tstrb       (s_tstrb),
    .s_axis_tlast       (s_tlast),
    .s_axis_tid         (s_tid),
    .s_axis_tdest       (s_tdest),
    .s_axis_tuser       (s_tuser),
    .s_axis_tvalid      (s_tvalid),
    .s_axis_tready      (s_tready),
    .s_axis_twakeup     (s_twakeup),
    .s_axis_tparity     ('0),            // Unused when ENABLE_PARITY=0

    // FUB streaming interface (to internal logic)
    .fub_axis_tdata     (fub_tdata),
    .fub_axis_tstrb     (fub_tstrb),
    .fub_axis_tlast     (fub_tlast),
    .fub_axis_tid       (fub_tid),
    .fub_axis_tdest     (fub_tdest),
    .fub_axis_tuser     (fub_tuser),
    .fub_axis_tvalid    (fub_tvalid),
    .fub_axis_tready    (fub_tready),
    .fub_axis_twakeup   (fub_twakeup),
    .fub_axis_tparity   (),              // Unused when ENABLE_PARITY=0

    // Status
    .busy               (s_busy),
    .parity_error       ()               // Unused when ENABLE_PARITY=0
);
```

### Clock-Gated Streaming

```systemverilog
// Clock-gated master for power efficiency
axis5_master_cg #(
    .AXIS_DATA_WIDTH        (128),
    .CG_IDLE_COUNT_WIDTH    (4)
) u_axis5_master_cg (
    .aclk                   (clk),
    .aresetn                (resetn),

    // Clock gating control
    .i_cg_enable            (1'b1),      // 1 = allow gating, 0 = clock always on
    .i_cg_idle_count        (4'd8),      // Idle cycles before the clock gates

    // Streaming interfaces (note the axis5_ prefix on the _cg variants)
    .fub_axis5_tdata        (fub_tdata),
    // ... remaining fub_axis5_* ports ...
    .m_axis5_tdata          (m_tdata),
    // ... remaining m_axis5_* ports ...

    // Status
    .busy                   (m_busy),
    .parity_error           (),
    .axis_clock_gating      (m_clk_gated)
);
```

**Port prefix warning:** the clock-gated variants name their streaming ports `fub_axis5_*` and `m_axis5_*` / `s_axis_*`, while the non-gated variants use `fub_axis_*` and `m_axis_*` / `s_axis_*`. Swapping a module for its `_cg` counterpart therefore requires renaming the FUB-side and master-side connections. See each module page for the exact port list.

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
| ACLK | Input | Stream clock (`aclk`) |
| ARESETN | Input | Active-low asynchronous reset (`aresetn`) |
| TDATA | Master to Slave | Stream data payload |
| TSTRB | Master to Slave | Byte strobes |
| TLAST | Master to Slave | End of packet/frame indicator |
| TID | Master to Slave | Stream identifier |
| TDEST | Master to Slave | Destination routing information |
| TUSER | Master to Slave | User-defined sideband data |
| TWAKEUP | Master to Slave | Wake-up signal (AXI5) |
| TPARITY | Master to Slave | Per-byte data parity (proprietary extension, optional) |
| TVALID | Master to Slave | Data valid indicator |
| TREADY | Slave to Master | Ready to accept data |

TKEEP is deliberately absent from this table because no AXIS5 module implements it.

### Flow Control

AXI5-Stream uses simple valid/ready handshaking:

1. **Data Transfer:** Occurs when TVALID and TREADY are both high
2. **Backpressure:** Slave deasserts TREADY to pause stream
3. **Source Stall:** Master deasserts TVALID when no data available
4. **Packet End:** TLAST indicates final beat of packet/frame

### Byte Qualification

These modules carry TSTRB only. The full ARM encoding, shown here for reference, needs both signals:

| TKEEP | TSTRB | Meaning |
|-------|-------|---------|
| 1 | 1 | Data byte |
| 1 | 0 | Position byte (placeholder) |
| 0 | 0 | Null byte (not transmitted) |
| 0 | 1 | Reserved |

**What these modules support:** only the TKEEP=1 rows are expressible. Treat TSTRB=1 as a data byte and TSTRB=0 as a position byte. Null bytes cannot be signalled. When connecting to IP that drives TKEEP, tie its TKEEP to all-ones and pass byte validity through TSTRB, or place a converter at the boundary.

---

## Design Notes

### FUB Interface Pattern

FUB stands for Functional Unit Block: the design-internal logic on the far side of the endpoint from the external stream bus. All AXIS5 modules use this pattern:
- **fub_axis_\*** (or **fub_axis5_\*** on the `_cg` variants) signals connect to internal logic
- **m_axis_\*** or **s_axis_\*** signals connect to the external stream bus
- A skid buffer sits between the FUB and external interfaces for timing closure. A skid buffer is a small registered elastic buffer (`gaxi_skid_buffer`, depth `SKID_DEPTH`) that absorbs backpressure so TREADY does not have to propagate combinationally across the endpoint.

### Migration from AXI4-Stream

AXIS5 modules keep the AXI4-Stream data path intact:
- Core protocol unchanged (TVALID/TREADY handshake)
- TWAKEUP can be tied to 0 for always-awake operation, or removed entirely with `ENABLE_WAKEUP=0`
- TPARITY is off by default (`ENABLE_PARITY=0`) and adds no ports of consequence when disabled
- TUSER width can match AXI4-Stream configurations

Neither generation implements TKEEP, so a design already using the AXIS4 modules will not gain or lose byte-qualification capability by moving to AXIS5.

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

The figures below are design targets, not measured silicon or post-route results. No synthesis or timing run for these modules is published in this repository, and achievable frequency depends heavily on data width, technology, and the surrounding logic. Treat them as order-of-magnitude guidance only.

| Metric | Value | Basis |
|--------|-------|-------|
| Throughput | 1 transfer per clock | Structural - skid buffer sustains full rate while TREADY is high |
| Latency (skid buffer) | 1-2 clock cycles | Registered path from input to output |
| Backpressure response | 1 clock cycle | TREADY deassertion is absorbed by the skid buffer |
| Maximum frequency | Design target only | Not characterized; no area or Fmax data published |

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
- Framework: `bin/TBClasses/components/axis4/`

---

**Last Updated:** 2026-07-19

---

## Navigation

- **[Back to rtl-amba Index](../index.md)**
- **[Back to Main Documentation Index](../../index.md)**
