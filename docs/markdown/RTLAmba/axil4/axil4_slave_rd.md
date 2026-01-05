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

# AXIL4 Slave Read

**Module:** `axil4_slave_rd.sv`
**Location:** `rtl/amba/axil4/`
**Status:** ✅ Production Ready

---

## Overview

The AXIL4 Slave Read module provides a buffered AXI4-Lite read interface for slave devices (memory, peripherals). It accepts read requests from an interconnect/master and forwards them to backend logic with elastic buffering for timing closure.

### Key Features

- ✅ **AXI4-Lite Slave:** Buffered read-only interface (AR and R channels)
- ✅ **Single-Beat Transactions:** No burst support
- ✅ **Elastic Buffering:** Decouples interconnect and backend timing
- ✅ **Activity Monitoring:** Busy signal for clock gating
- ✅ **Minimal Latency:** 1-cycle buffer overhead per channel

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `AXIL_ADDR_WIDTH` | int | 32 | Address bus width |
| `AXIL_DATA_WIDTH` | int | 32 | Data bus width (32 or 64) |
| `SKID_DEPTH_AR` | int | 2 | AR channel buffer depth (2^N entries) |
| `SKID_DEPTH_R` | int | 4 | R channel buffer depth (2^N entries) |

---

## Port Groups

### Slave Interface (Input Side from Interconnect)

**Read Address Channel (AR):**
| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `s_axil_araddr` | Input | AW | Read address (from interconnect) |
| `s_axil_arprot` | Input | 3 | Protection attributes |
| `s_axil_arvalid` | Input | 1 | Address valid |
| `s_axil_arready` | Output | 1 | Address ready (buffer status) |

**Read Data Channel (R):**
| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `s_axil_rdata` | Output | DW | Read data (to interconnect) |
| `s_axil_rresp` | Output | 2 | Read response |
| `s_axil_rvalid` | Output | 1 | Data valid |
| `s_axil_rready` | Input | 1 | Data ready |

### Backend Interface (Output Side to Memory/Logic)

**Read Address Channel (AR):**
| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `fub_araddr` | Output | AW | Read address (to backend) |
| `fub_arprot` | Output | 3 | Protection attributes |
| `fub_arvalid` | Output | 1 | Address valid |
| `fub_arready` | Input | 1 | Address ready (from backend) |

**Read Data Channel (R):**
| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `fub_rdata` | Input | DW | Read data (from backend) |
| `fub_rresp` | Input | 2 | Read response |
| `fub_rvalid` | Input | 1 | Data valid |
| `fub_rready` | Output | 1 | Data ready |

### Status Outputs

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `busy` | Output | 1 | Interface active (for clock gating) |

---

## Usage Example

```systemverilog
axil4_slave_rd #(
    .AXIL_ADDR_WIDTH(32),
    .AXIL_DATA_WIDTH(32),
    .SKID_DEPTH_AR(2),
    .SKID_DEPTH_R(4)
) u_axil_slave_rd (
    .aclk           (axi_clk),
    .aresetn        (axi_resetn),

    // Slave interface (from interconnect)
    .s_axil_araddr  (interconnect_araddr),
    .s_axil_arprot  (interconnect_arprot),
    .s_axil_arvalid (interconnect_arvalid),
    .s_axil_arready (interconnect_arready),

    .s_axil_rdata   (interconnect_rdata),
    .s_axil_rresp   (interconnect_rresp),
    .s_axil_rvalid  (interconnect_rvalid),
    .s_axil_rready  (interconnect_rready),

    // Backend interface (to memory/peripheral)
    .fub_araddr     (mem_araddr),
    .fub_arprot     (mem_arprot),
    .fub_arvalid    (mem_arvalid),
    .fub_arready    (mem_arready),

    .fub_rdata      (mem_rdata),
    .fub_rresp      (mem_rresp),
    .fub_rvalid     (mem_rvalid),
    .fub_rready     (mem_rready),

    // Status
    .busy           (rd_busy)
);
```

---

## Design Notes

- **Signal Flow:** Interconnect → AR Buffer → Backend → R Buffer → Interconnect
- **Use Case:** Memory controllers, peripheral slaves, register blocks
- **Buffering:** Allows backend to respond at its own pace without stalling interconnect

---

## Related Modules

- **[axil4_slave_wr](axil4_slave_wr.md)** - Slave write counterpart
- **[axil4_master_rd](axil4_master_rd.md)** - Master read interface
- **[axil4_slave_rd_mon](axil4_slave_rd_mon.md)** - Slave read with monitoring
- **[axil4_slave_rd_cg](axil4_clock_gating_guide.md)** - Clock-gated version

---

**Last Updated:** 2025-10-20

---

## Navigation

- **[← Back to AXIL4 Index](README.md)**
- **[← Back to RTLAmba Index](../README.md)**
- **[← Back to Main Documentation Index](../../index.md)**
