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

# AXIS5 Master

**Module:** `axis5_master.sv`
**Location:** `rtl/amba/axis5/`
**Status:** Production Ready

---

## Overview

The AXIS5 Master module implements an AXI5-Stream master interface with AMBA5 extensions including wake-up signaling for power management and optional parity for data integrity. It provides buffering through an internal skid buffer for improved system performance.

### Key Features

- Full AXI5-Stream protocol compliance
- TWAKEUP: Wake-up signaling for power management
- TPARITY: Optional parity protection (1 bit per byte)
- Internal skid buffer for backpressure handling
- Configurable data, ID, destination, and user signal widths
- Parity error detection and reporting
- Busy status indication

### AXIS5 Extensions Over AXIS4

| Feature | AXIS4 | AXIS5 |
|---------|-------|-------|
| Wake-up signal | None | TWAKEUP (configurable) |
| Data parity | None | TPARITY (1 bit per byte, configurable) |
| Parity error detection | None | Built-in error flag |

---

## Module Architecture

```mermaid
flowchart TB
    subgraph INPUT["FUB Interface (Input)"]
        fub_tdata["fub_axis_tdata"]
        fub_tvalid["fub_axis_tvalid"]
        fub_tready["fub_axis_tready"]
        fub_twakeup["fub_axis_twakeup"]
        fub_tparity["fub_axis_tparity"]
    end

    subgraph PACK["Packet Packing"]
        pack["Pack signals based on<br/>ENABLE_WAKEUP/ENABLE_PARITY"]
    end

    subgraph SKID["Skid Buffer"]
        sb["gaxi_skid_buffer<br/>Depth: SKID_DEPTH"]
    end

    subgraph UNPACK["Packet Unpacking"]
        unpack["Unpack to AXIS5 signals"]
    end

    subgraph PARITY["Parity Check (Optional)"]
        calc["Calculate parity<br/>per byte"]
        cmp["Compare with<br/>received parity"]
        err["parity_error<br/>flag"]
    end

    subgraph OUTPUT["Master AXIS5 Interface"]
        m_tdata["m_axis_tdata"]
        m_tvalid["m_axis_tvalid"]
        m_tready["m_axis_tready"]
        m_twakeup["m_axis_twakeup"]
        m_tparity["m_axis_tparity"]
    end

    INPUT --> PACK
    PACK --> SKID
    SKID --> UNPACK
    UNPACK --> OUTPUT
    OUTPUT --> PARITY
    PARITY --> err

    style PARITY fill:#fff4e6
    style err fill:#ffe6e6
```

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| SKID_DEPTH | int | 4 | Internal skid buffer depth |
| AXIS_DATA_WIDTH | int | 32 | AXIS data bus width (must be multiple of 8) |
| AXIS_ID_WIDTH | int | 8 | AXIS ID signal width (0 to disable) |
| AXIS_DEST_WIDTH | int | 4 | AXIS TDEST signal width (0 to disable) |
| AXIS_USER_WIDTH | int | 1 | AXIS TUSER signal width (0 to disable) |
| ENABLE_WAKEUP | bit | 1 | Enable TWAKEUP signal (1=enabled) |
| ENABLE_PARITY | bit | 0 | Enable TPARITY signal (1=enabled) |
| DW | int | AXIS_DATA_WIDTH | Data width short name (calculated) |
| IW | int | AXIS_ID_WIDTH | ID width short name (calculated) |
| DESTW | int | AXIS_DEST_WIDTH | DEST width short name (calculated) |
| UW | int | AXIS_USER_WIDTH | USER width short name (calculated) |
| SW | int | DW/8 | Strobe width in bytes (calculated) |
| PW | int | SW | Parity width - 1 bit per byte (calculated) |

---

## Ports

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| aclk | 1 | Input | AXIS clock |
| aresetn | 1 | Input | AXIS active-low asynchronous reset |

### FUB AXIS5 Interface (Input Side)

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| fub_axis_tdata | DW | Input | Transfer data |
| fub_axis_tstrb | SW | Input | Transfer byte strobes |
| fub_axis_tlast | 1 | Input | Last transfer in packet |
| fub_axis_tid | IW_WIDTH | Input | Transfer ID (optional) |
| fub_axis_tdest | DESTW_WIDTH | Input | Transfer destination (optional) |
| fub_axis_tuser | UW_WIDTH | Input | Transfer user-defined signals (optional) |
| fub_axis_tvalid | 1 | Input | Transfer valid |
| fub_axis_tready | 1 | Output | Transfer ready (skid buffer not full) |
| fub_axis_twakeup | 1 | Input | Wake-up signal (AXIS5 extension) |
| fub_axis_tparity | PW_WIDTH | Input | Data parity per byte (AXIS5 extension) |

### Master AXIS5 Interface (Output Side)

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| m_axis_tdata | DW | Output | Transfer data |
| m_axis_tstrb | SW | Output | Transfer byte strobes |
| m_axis_tlast | 1 | Output | Last transfer in packet |
| m_axis_tid | IW_WIDTH | Output | Transfer ID (optional) |
| m_axis_tdest | DESTW_WIDTH | Output | Transfer destination (optional) |
| m_axis_tuser | UW_WIDTH | Output | Transfer user-defined signals (optional) |
| m_axis_tvalid | 1 | Output | Transfer valid |
| m_axis_tready | 1 | Input | Transfer ready from downstream |
| m_axis_twakeup | 1 | Output | Wake-up signal (AXIS5 extension) |
| m_axis_tparity | PW_WIDTH | Output | Data parity per byte (AXIS5 extension) |

### Status Outputs

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| busy | 1 | Output | Module busy (data in buffer or input valid) |
| parity_error | 1 | Output | Parity error detected (sticky flag) |

---

## Functionality

### Skid Buffer Operation

The module uses an internal `gaxi_skid_buffer` to:
- Accept incoming transfers even when downstream is not ready
- Prevent backpressure propagation
- Provide registered outputs for timing closure
- Track buffer occupancy via `busy` signal

### Packet Packing/Unpacking

**Conditional packing based on configuration:**

```systemverilog
// Full feature set (ENABLE_WAKEUP=1, ENABLE_PARITY=1)
{tdata, tstrb, tlast, tid, tdest, tuser, twakeup, tparity}

// Wake-up only (ENABLE_WAKEUP=1, ENABLE_PARITY=0)
{tdata, tstrb, tlast, tid, tdest, tuser, twakeup}

// Parity only (ENABLE_WAKEUP=0, ENABLE_PARITY=1)
{tdata, tstrb, tlast, tid, tdest, tuser, tparity}

// Base AXIS4 (ENABLE_WAKEUP=0, ENABLE_PARITY=0)
{tdata, tstrb, tlast, tid, tdest, tuser}
```

### Parity Checking (Optional)

When `ENABLE_PARITY=1`:
1. Calculate odd parity for each data byte: `parity[i] = ^tdata[i*8 +: 8]`
2. Compare calculated parity with received `m_axis_tparity`
3. Set `parity_error` flag on mismatch (sticky, cleared by reset)
4. Parity check occurs on valid output transfers

### Busy Signal

The `busy` output indicates:
- Input side has valid data (`fub_axis_tvalid`)
- Skid buffer contains data (`int_t_count > 0`)

---

## Timing Diagrams

### Basic Transfer with Wake-up

<!-- TODO: Add wavedrom timing diagram for AXIS5 transfer with wake-up -->
```
TODO: Wavedrom timing diagram showing:
- aclk
- fub_axis_tvalid/tready
- fub_axis_tdata
- fub_axis_tlast
- fub_axis_twakeup (AXIS5 extension)
- m_axis_tvalid/tready
- m_axis_tdata
- m_axis_twakeup
- busy
```

### Transfer with Parity Error

<!-- TODO: Add wavedrom timing diagram for parity error detection -->
```
TODO: Wavedrom timing diagram showing:
- aclk
- m_axis_tdata
- m_axis_tparity (received)
- calculated_parity
- parity_mismatch
- parity_error (sticky flag)
```

### Skid Buffer Backpressure

<!-- TODO: Add wavedrom timing diagram for skid buffer operation -->
```
TODO: Wavedrom timing diagram showing:
- aclk
- fub_axis_tvalid/tready
- m_axis_tvalid/tready (downstream blocked)
- int_t_count (buffer fill level)
- busy
```

---

## Usage Example

### Basic Configuration

```systemverilog
axis5_master #(
    .SKID_DEPTH       (4),
    .AXIS_DATA_WIDTH  (64),
    .AXIS_ID_WIDTH    (8),
    .AXIS_DEST_WIDTH  (4),
    .AXIS_USER_WIDTH  (1),
    .ENABLE_WAKEUP    (1),
    .ENABLE_PARITY    (0)
) u_axis5_master (
    .aclk                (axis_clk),
    .aresetn             (axis_rst_n),

    // FUB interface (from upstream)
    .fub_axis_tdata      (fub_tdata),
    .fub_axis_tstrb      (fub_tstrb),
    .fub_axis_tlast      (fub_tlast),
    .fub_axis_tid        (fub_tid),
    .fub_axis_tdest      (fub_tdest),
    .fub_axis_tuser      (fub_tuser),
    .fub_axis_tvalid     (fub_tvalid),
    .fub_axis_tready     (fub_tready),
    .fub_axis_twakeup    (fub_twakeup),
    .fub_axis_tparity    (8'h00),  // Not used when ENABLE_PARITY=0

    // Master AXIS5 interface (to downstream)
    .m_axis_tdata        (m_axis_tdata),
    .m_axis_tstrb        (m_axis_tstrb),
    .m_axis_tlast        (m_axis_tlast),
    .m_axis_tid          (m_axis_tid),
    .m_axis_tdest        (m_axis_tdest),
    .m_axis_tuser        (m_axis_tuser),
    .m_axis_tvalid       (m_axis_tvalid),
    .m_axis_tready       (m_axis_tready),
    .m_axis_twakeup      (m_axis_twakeup),
    .m_axis_tparity      (),  // Not used when ENABLE_PARITY=0

    // Status
    .busy                (axis_busy),
    .parity_error        ()  // Not used when ENABLE_PARITY=0
);
```

### With Parity Protection

```systemverilog
axis5_master #(
    .AXIS_DATA_WIDTH  (32),
    .ENABLE_WAKEUP    (1),
    .ENABLE_PARITY    (1)  // Enable parity checking
) u_axis5_master_parity (
    .aclk                (axis_clk),
    .aresetn             (axis_rst_n),

    // FUB interface with parity
    .fub_axis_tdata      (fub_tdata),
    .fub_axis_tstrb      (fub_tstrb),
    .fub_axis_tlast      (fub_tlast),
    .fub_axis_tid        (fub_tid),
    .fub_axis_tdest      (fub_tdest),
    .fub_axis_tuser      (fub_tuser),
    .fub_axis_tvalid     (fub_tvalid),
    .fub_axis_tready     (fub_tready),
    .fub_axis_twakeup    (fub_twakeup),
    .fub_axis_tparity    (fub_tparity),  // 4 bits for 32-bit data

    // Master AXIS5 interface
    .m_axis_tdata        (m_axis_tdata),
    .m_axis_tstrb        (m_axis_tstrb),
    .m_axis_tlast        (m_axis_tlast),
    .m_axis_tid          (m_axis_tid),
    .m_axis_tdest        (m_axis_tdest),
    .m_axis_tuser        (m_axis_tuser),
    .m_axis_tvalid       (m_axis_tvalid),
    .m_axis_tready       (m_axis_tready),
    .m_axis_twakeup      (m_axis_twakeup),
    .m_axis_tparity      (m_axis_tparity),

    // Status - monitor parity errors
    .busy                (axis_busy),
    .parity_error        (axis_parity_err)  // Sticky error flag
);

// Error handling
always_ff @(posedge axis_clk or negedge axis_rst_n) begin
    if (!axis_rst_n)
        error_count <= '0;
    else if (axis_parity_err && !prev_parity_err)
        error_count <= error_count + 1;
end
```

---

## Design Notes

### AXIS5 vs AXIS4 Differences

| Feature | AXIS4 | AXIS5 |
|---------|-------|-------|
| Wake-up signal | Not supported | TWAKEUP (optional) |
| Data parity | Not supported | TPARITY per byte (optional) |
| Power management | Limited | Enhanced via TWAKEUP |
| Data integrity | CRC/checksum in TUSER | Built-in parity option |

### Skid Buffer Sizing

- **Typical depth:** 4-8 entries
- Deeper buffers:
  - Absorb longer downstream stalls
  - Increase area and latency
- Shallower buffers:
  - Lower latency
  - May cause upstream backpressure

**Recommendation:** Use depth 4 for most applications, increase if downstream frequently stalls.

### Parity Implementation

When `ENABLE_PARITY=1`:
- **Overhead:** 1 bit per data byte (12.5% for 8-bit bytes)
- **Detection:** Single-bit errors only (odd parity)
- **Correction:** None - error flag only
- **Use case:** Low-cost error detection in reliable environments

For stronger protection, use:
- CRC in TUSER field
- ECC (external module)
- End-to-end checksums at packet level

### Optional Signal Widths

Setting width parameters to 0 disables optional signals:
- `AXIS_ID_WIDTH=0` → TID tied to 0, saves area
- `AXIS_DEST_WIDTH=0` → TDEST tied to 0
- `AXIS_USER_WIDTH=0` → TUSER tied to 0

Internal logic uses `IW_WIDTH = (IW > 0) ? IW : 1` to avoid zero-width signals.

---

## Related Documentation

- **[AXIS5 Slave](axis5_slave.md)** - AXIS5 slave interface
- **[AXIS5 Master CG](axis5_master_cg.md)** - Clock-gated variant with power management
- **[AXIS5 Slave CG](axis5_slave_cg.md)** - Clock-gated slave variant
- **[AXIS4 Master](../fabric/axis_master.md)** - AXIS4 version for comparison
- **[AMBA5 Overview](../overview.md)** - AMBA5 specifications and extensions

---

## Navigation

- **[← Back to AXIS5 Index](README.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
