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

# AXIL4 Slave Write

**Module:** `axil4_slave_wr.sv`
**Location:** `rtl/amba/axil4/`
**Status:** ✅ Production Ready

---

## Overview

The AXIL4 Slave Write module provides a buffered AXI4-Lite write interface for slave devices (memory, peripherals). It accepts write requests from an interconnect/master and forwards them to backend logic with elastic buffering for timing closure.

### Key Features

- ✅ **AXI4-Lite Slave:** Buffered write-only interface (AW, W, B channels)
- ✅ **Single-Beat Transactions:** No burst support
- ✅ **Byte Strobes:** WSTRB support for partial writes
- ✅ **Elastic Buffering:** Decouples interconnect and backend timing
- ✅ **Activity Monitoring:** Busy signal for clock gating
- ✅ **Minimal Latency:** 1-cycle buffer overhead per channel

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `AXIL_ADDR_WIDTH` | int | 32 | Address bus width |
| `AXIL_DATA_WIDTH` | int | 32 | Data bus width (32 or 64) |
| `SKID_DEPTH_AW` | int | 2 | AW channel buffer depth (2^N entries) |
| `SKID_DEPTH_W` | int | 2 | W channel buffer depth (2^N entries) |
| `SKID_DEPTH_B` | int | 2 | B channel buffer depth (2^N entries) |

---

## Port Groups

### Slave Interface (Input Side from Interconnect)

**Write Address Channel (AW):**
| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `s_axil_awaddr` | Input | AW | Write address (from interconnect) |
| `s_axil_awprot` | Input | 3 | Protection attributes |
| `s_axil_awvalid` | Input | 1 | Address valid |
| `s_axil_awready` | Output | 1 | Address ready (buffer status) |

**Write Data Channel (W):**
| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `s_axil_wdata` | Input | DW | Write data (from interconnect) |
| `s_axil_wstrb` | Input | DW/8 | Write strobes |
| `s_axil_wvalid` | Input | 1 | Data valid |
| `s_axil_wready` | Output | 1 | Data ready (buffer status) |

**Write Response Channel (B):**
| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `s_axil_bresp` | Output | 2 | Write response (to interconnect) |
| `s_axil_bvalid` | Output | 1 | Response valid |
| `s_axil_bready` | Input | 1 | Response ready |

### Backend Interface (Output Side to Memory/Logic)

**Write Address Channel (AW):**
| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `fub_awaddr` | Output | AW | Write address (to backend) |
| `fub_awprot` | Output | 3 | Protection attributes |
| `fub_awvalid` | Output | 1 | Address valid |
| `fub_awready` | Input | 1 | Address ready (from backend) |

**Write Data Channel (W):**
| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `fub_wdata` | Output | DW | Write data (to backend) |
| `fub_wstrb` | Output | DW/8 | Write strobes |
| `fub_wvalid` | Output | 1 | Data valid |
| `fub_wready` | Input | 1 | Data ready (from backend) |

**Write Response Channel (B):**
| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `fub_bresp` | Input | 2 | Write response (from backend) |
| `fub_bvalid` | Input | 1 | Response valid |
| `fub_bready` | Output | 1 | Response ready |

### Status Outputs

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `busy` | Output | 1 | Interface active (for clock gating) |

---

## Usage Example

```systemverilog
axil4_slave_wr #(
    .AXIL_ADDR_WIDTH(32),
    .AXIL_DATA_WIDTH(32),
    .SKID_DEPTH_AW(2),
    .SKID_DEPTH_W(2),
    .SKID_DEPTH_B(2)
) u_axil_slave_wr (
    .aclk           (axi_clk),
    .aresetn        (axi_resetn),

    // Slave interface (from interconnect)
    .s_axil_awaddr  (interconnect_awaddr),
    .s_axil_awprot  (interconnect_awprot),
    .s_axil_awvalid (interconnect_awvalid),
    .s_axil_awready (interconnect_awready),

    .s_axil_wdata   (interconnect_wdata),
    .s_axil_wstrb   (interconnect_wstrb),
    .s_axil_wvalid  (interconnect_wvalid),
    .s_axil_wready  (interconnect_wready),

    .s_axil_bresp   (interconnect_bresp),
    .s_axil_bvalid  (interconnect_bvalid),
    .s_axil_bready  (interconnect_bready),

    // Backend interface (to memory/peripheral)
    .fub_awaddr     (mem_awaddr),
    .fub_awprot     (mem_awprot),
    .fub_awvalid    (mem_awvalid),
    .fub_awready    (mem_awready),

    .fub_wdata      (mem_wdata),
    .fub_wstrb      (mem_wstrb),
    .fub_wvalid     (mem_wvalid),
    .fub_wready     (mem_wready),

    .fub_bresp      (mem_bresp),
    .fub_bvalid     (mem_bvalid),
    .fub_bready     (mem_bready),

    // Status
    .busy           (wr_busy)
);
```

---

## Design Notes

- **Signal Flow:** Interconnect → AW/W Buffers → Backend → B Buffer → Interconnect
- **Use Case:** Memory controllers, peripheral slaves, register blocks
- **Buffering:** Allows backend to respond at its own pace without stalling interconnect
- **Write Strobes:** Backend must honor WSTRB for partial word writes

---

## Related Modules

- **[axil4_slave_rd](axil4_slave_rd.md)** - Slave read counterpart
- **[axil4_master_wr](axil4_master_wr.md)** - Master write interface
- **[axil4_slave_wr_mon](axil4_slave_wr_mon.md)** - Slave write with monitoring
- **[axil4_slave_wr_cg](axil4_clock_gating_guide.md)** - Clock-gated version

---

**Last Updated:** 2025-10-20

---

## Navigation

- **[← Back to AXIL4 Index](README.md)**
- **[← Back to RTLAmba Index](../README.md)**
- **[← Back to Main Documentation Index](../../index.md)**
