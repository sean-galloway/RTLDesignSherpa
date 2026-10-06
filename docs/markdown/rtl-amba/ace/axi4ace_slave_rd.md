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

# axi4ace_slave_rd

An AXI4 + ACE read slave module that buffers AR and R channels while carrying the ACE `ARSNOOP[3:0]` transaction-type field from the slave interface to the backend.

## Overview

The `axi4ace_slave_rd` module is the ACE extension of `axi4_slave_rd`. It receives AXI4 read requests with the ACE `ARSNOOP[3:0]` field on the `s_axi_*` interface, buffers them, and presents them on the `fub_axi_*` backend interface. It is a transport module: it does not generate read data or interpret snoop encodings.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| SKID_DEPTH_AR | int | 2 | Address channel skid buffer depth in entries (2..8 inclusive) |
| SKID_DEPTH_R | int | 4 | Read data channel skid buffer depth in entries (2..8 inclusive) |
| AXI_ID_WIDTH | int | 8 | AXI transaction ID width |
| AXI_ADDR_WIDTH | int | 32 | AXI address bus width |
| AXI_DATA_WIDTH | int | 32 | AXI data bus width |
| AXI_USER_WIDTH | int | 1 | AXI user signal width |
| AXI_WSTRB_WIDTH | int | AXI_DATA_WIDTH/8 | Write strobe width (unused, kept for naming consistency) |
| AW | int | AXI_ADDR_WIDTH | Short alias for address width |
| DW | int | AXI_DATA_WIDTH | Short alias for data width |
| IW | int | AXI_ID_WIDTH | Short alias for ID width |
| SW | int | AXI_WSTRB_WIDTH | Short alias for strobe width |
| UW | int | AXI_USER_WIDTH | Short alias for user width |
| ARSize | int | IW+AW+8+3+2+1+4+3+4+4+UW+4 | Packed AR skid payload width |
| RSize | int | IW+DW+2+1+UW | Packed R skid payload width |

## Ports

### Module Declaration

```systemverilog
module axi4ace_slave_rd #(
    parameter int SKID_DEPTH_AR     = 2,
    parameter int SKID_DEPTH_R      = 4,
    parameter int AXI_ID_WIDTH      = 8,
    parameter int AXI_ADDR_WIDTH    = 32,
    parameter int AXI_DATA_WIDTH    = 32,
    parameter int AXI_USER_WIDTH    = 1,
    parameter int AXI_WSTRB_WIDTH   = AXI_DATA_WIDTH / 8,
    parameter int AW       = AXI_ADDR_WIDTH,
    parameter int DW       = AXI_DATA_WIDTH,
    parameter int IW       = AXI_ID_WIDTH,
    parameter int SW       = AXI_WSTRB_WIDTH,
    parameter int UW       = AXI_USER_WIDTH,
    parameter int ARSize   = IW+AW+8+3+2+1+4+3+4+4+UW+4,
    parameter int RSize    = IW+DW+2+1+UW
) (
    // Global Clock and Reset
    input  logic aclk,
    input  logic aresetn,

    // Slave AXI Interface (Input Side)
    // Read address channel (AR)
    input  logic [IW-1:0]                s_axi_arid,
    input  logic [AW-1:0]                s_axi_araddr,
    input  logic [7:0]                   s_axi_arlen,
    input  logic [2:0]                   s_axi_arsize,
    input  logic [1:0]                   s_axi_arburst,
    input  logic                         s_axi_arlock,
    input  logic [3:0]                   s_axi_arcache,
    input  logic [2:0]                   s_axi_arprot,
    input  logic [3:0]                   s_axi_arqos,
    input  logic [3:0]                   s_axi_arregion,
    input  logic [UW-1:0]                s_axi_aruser,
    input  logic [3:0]                   s_axi_arsnoop,
    input  logic                         s_axi_arvalid,
    output logic                         s_axi_arready,

    // Read data channel (R)
    output logic [IW-1:0]                s_axi_rid,
    output logic [DW-1:0]                s_axi_rdata,
    output logic [1:0]                   s_axi_rresp,
    output logic                         s_axi_rlast,
    output logic [UW-1:0]                s_axi_ruser,
    output logic                         s_axi_rvalid,
    input  logic                         s_axi_rready,

    // Master AXI Interface (Output Side to memory or backend)
    // Read address channel (AR)
    output logic [IW-1:0]                fub_axi_arid,
    output logic [AW-1:0]                fub_axi_araddr,
    output logic [7:0]                   fub_axi_arlen,
    output logic [2:0]                   fub_axi_arsize,
    output logic [1:0]                   fub_axi_arburst,
    output logic                         fub_axi_arlock,
    output logic [3:0]                   fub_axi_arcache,
    output logic [2:0]                   fub_axi_arprot,
    output logic [3:0]                   fub_axi_arqos,
    output logic [3:0]                   fub_axi_arregion,
    output logic [UW-1:0]                fub_axi_aruser,
    output logic [3:0]                   fub_axi_arsnoop,
    output logic                         fub_axi_arvalid,
    input  logic                         fub_axi_arready,

    // Read data channel (R)
    input  logic [IW-1:0]                fub_axi_rid,
    input  logic [DW-1:0]                fub_axi_rdata,
    input  logic [1:0]                   fub_axi_rresp,
    input  logic                         fub_axi_rlast,
    input  logic [UW-1:0]                fub_axi_ruser,
    input  logic                         fub_axi_rvalid,
    output logic                         fub_axi_rready,

    // Status outputs for clock gating
    output logic                         busy
);
```

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| aclk | 1 | Input | AXI clock |
| aresetn | 1 | Input | AXI active-low reset |

### Slave AXI Interface (Input Side)

#### Read Address Channel (AR)
| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| s_axi_arid | AXI_ID_WIDTH | Input | Read address ID |
| s_axi_araddr | AXI_ADDR_WIDTH | Input | Read address |
| s_axi_arlen | 8 | Input | Burst length, AXI-encoded: beats - 1 |
| s_axi_arsize | 3 | Input | Transfer size (bytes per beat) |
| s_axi_arburst | 2 | Input | Burst type (FIXED, INCR, WRAP) |
| s_axi_arlock | 1 | Input | Lock type (atomic access) |
| s_axi_arcache | 4 | Input | Cache attributes |
| s_axi_arprot | 3 | Input | Protection attributes |
| s_axi_arqos | 4 | Input | Quality of Service |
| s_axi_arregion | 4 | Input | Region identifier |
| s_axi_aruser | AXI_USER_WIDTH | Input | User-defined signals |
| s_axi_arsnoop | 4 | Input | ACE read transaction type |
| s_axi_arvalid | 1 | Input | Read address valid |
| s_axi_arready | 1 | Output | Read address ready |

#### Read Data Channel (R)
| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| s_axi_rid | AXI_ID_WIDTH | Output | Read data ID |
| s_axi_rdata | AXI_DATA_WIDTH | Output | Read data |
| s_axi_rresp | 2 | Output | Read response (OKAY, EXOKAY, SLVERR, DECERR) |
| s_axi_rlast | 1 | Output | Last read transfer in burst |
| s_axi_ruser | AXI_USER_WIDTH | Output | User-defined signals |
| s_axi_rvalid | 1 | Output | Read data valid |
| s_axi_rready | 1 | Input | Read data ready |

### Master AXI Interface (Output Side - FUB)

#### Read Address Channel (AR)
| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| fub_axi_arid | AXI_ID_WIDTH | Output | Read address ID |
| fub_axi_araddr | AXI_ADDR_WIDTH | Output | Read address |
| fub_axi_arlen | 8 | Output | Burst length, AXI-encoded: beats - 1 |
| fub_axi_arsize | 3 | Output | Transfer size (bytes per beat) |
| fub_axi_arburst | 2 | Output | Burst type (FIXED, INCR, WRAP) |
| fub_axi_arlock | 1 | Output | Lock type (atomic access) |
| fub_axi_arcache | 4 | Output | Cache attributes |
| fub_axi_arprot | 3 | Output | Protection attributes |
| fub_axi_arqos | 4 | Output | Quality of Service |
| fub_axi_arregion | 4 | Output | Region identifier |
| fub_axi_aruser | AXI_USER_WIDTH | Output | User-defined signals |
| fub_axi_arsnoop | 4 | Output | ACE read transaction type |
| fub_axi_arvalid | 1 | Output | Read address valid |
| fub_axi_arready | 1 | Input | Read address ready |

#### Read Data Channel (R)
| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| fub_axi_rid | AXI_ID_WIDTH | Input | Read data ID |
| fub_axi_rdata | AXI_DATA_WIDTH | Input | Read data |
| fub_axi_rresp | 2 | Input | Read response (OKAY, EXOKAY, SLVERR, DECERR) |
| fub_axi_rlast | 1 | Input | Last read transfer in burst |
| fub_axi_ruser | AXI_USER_WIDTH | Input | User-defined signals |
| fub_axi_rvalid | 1 | Input | Read data valid |
| fub_axi_rready | 1 | Output | Read data ready |

### Status Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| busy | 1 | Output | Module activity indicator for clock gating |

## Functional Description

### Dual Buffer Design

The module buffers AR from the slave side to the backend and R from the backend back to the slave side:

1. **AR Channel Buffer**: Receives `s_axi_ar*` and presents `fub_axi_ar*`, including `ARSNOOP`
2. **R Channel Buffer**: Receives `fub_axi_r*` and presents `s_axi_r*`

### Busy Signal Generation

```systemverilog
assign busy = (int_ar_count > 0) || (int_r_count > 0) ||
                s_axi_arvalid || fub_axi_rvalid;
```

## ACE Notes

- `ARSNOOP[3:0]` is carried straight through from `s_axi_arsnoop` to `fub_axi_arsnoop`
- The module does not generate `RACK`; that handshake is produced by the upstream master
- IDs (`ARID`/`RID`) are carried end-to-end; the module performs no ID matching
- `AXI_WSTRB_WIDTH` is present only for naming consistency with the write slave and is unused

## Related Modules

- **axi4ace_slave_rd_monlite**: Lite-monitor wrapper for this core
- **axi4ace_master_rd**: Complementary ACE read master
- **axi4_slave_rd**: AXI4-only base module
- **gaxi_skid_buffer**: Underlying buffer infrastructure

---

## Navigation

- **[← Back to ACE Index](README.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
