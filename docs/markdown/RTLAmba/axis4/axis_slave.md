# axis_slave

An AXI4-Stream slave module that provides high-throughput streaming data reception with configurable buffering and comprehensive support for all AXI4-Stream sideband signals including ID, DEST, and USER channels.

## Overview

The `axis_slave` module implements a complete AXI4-Stream slave interface with integrated skid buffering for optimal streaming performance. It supports the full AXI4-Stream protocol with configurable data widths, optional sideband signals, and intelligent buffer management for streaming data applications.

## Module Declaration

```systemverilog
module axis_slave #(
    parameter int SKID_DEPTH         = 4,
    parameter int AXIS_DATA_WIDTH    = 32,
    parameter int AXIS_ID_WIDTH      = 8,
    parameter int AXIS_DEST_WIDTH    = 4,
    parameter int AXIS_USER_WIDTH    = 1,

    // Short and calculated params
    parameter int DW       = AXIS_DATA_WIDTH,
    parameter int IW       = AXIS_ID_WIDTH,
    parameter int DESTW    = AXIS_DEST_WIDTH,
    parameter int UW       = AXIS_USER_WIDTH,
    parameter int SW       = DW / 8,
    parameter int IW_WIDTH = (IW > 0) ? IW : 1,
    parameter int DESTW_WIDTH = (DESTW > 0) ? DESTW : 1,
    parameter int UW_WIDTH = (UW > 0) ? UW : 1,
    parameter int TSize    = DW+SW+1+IW_WIDTH+DESTW_WIDTH+UW_WIDTH
) (
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Slave AXI4-Stream Interface (Input Side from interconnect)
    input  logic [DW-1:0]              s_axis_tdata,
    input  logic [SW-1:0]              s_axis_tstrb,
    input  logic                       s_axis_tlast,
    input  logic [IW_WIDTH-1:0]        s_axis_tid,
    input  logic [DESTW_WIDTH-1:0]     s_axis_tdest,
    input  logic [UW_WIDTH-1:0]        s_axis_tuser,
    input  logic                       s_axis_tvalid,
    output logic                       s_axis_tready,

    // Master AXI4-Stream Interface (Output Side to backend)
    output logic [DW-1:0]              fub_axis_tdata,
    output logic [SW-1:0]              fub_axis_tstrb,
    output logic                       fub_axis_tlast,
    output logic [IW_WIDTH-1:0]        fub_axis_tid,
    output logic [DESTW_WIDTH-1:0]     fub_axis_tdest,
    output logic [UW_WIDTH-1:0]        fub_axis_tuser,
    output logic                       fub_axis_tvalid,
    input  logic                       fub_axis_tready,

    // Status outputs for clock gating
    output logic                       busy
);
```

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| SKID_DEPTH | int | 4 | Skid buffer depth (2^N entries) |
| AXIS_DATA_WIDTH | int | 32 | AXI4-Stream data bus width (bytes) |
| AXIS_ID_WIDTH | int | 8 | Stream ID width (0 to disable) |
| AXIS_DEST_WIDTH | int | 4 | Destination width (0 to disable) |
| AXIS_USER_WIDTH | int | 1 | User signal width (0 to disable) |

## Ports

### Slave AXI4-Stream Interface (Input from Interconnect)

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| s_axis_tdata | DW | Input | Stream data |
| s_axis_tstrb | SW | Input | Data strobes (byte-valid indicators) |
| s_axis_tlast | 1 | Input | Last transfer in packet |
| s_axis_tid | IW | Input | Stream ID (routing/reordering) |
| s_axis_tdest | DESTW | Input | Destination routing |
| s_axis_tuser | UW | Input | User-defined sideband |
| s_axis_tvalid | 1 | Input | Data valid |
| s_axis_tready | 1 | Output | Ready to accept data |

### Backend Interface (Output to Processing Logic)

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| fub_axis_tdata | DW | Output | Stream data (to backend) |
| fub_axis_tstrb | SW | Output | Data strobes |
| fub_axis_tlast | 1 | Output | Last transfer in packet |
| fub_axis_tid | IW | Output | Stream ID |
| fub_axis_tdest | DESTW | Output | Destination routing |
| fub_axis_tuser | UW | Output | User-defined sideband |
| fub_axis_tvalid | 1 | Output | Data valid (to backend) |
| fub_axis_tready | 1 | Input | Backend ready |

### Status

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| busy | 1 | Output | Interface active (for clock gating) |

## Features

- **Full AXI4-Stream Protocol:** Support for all optional sideband signals
- **Elastic Buffering:** Skid buffer decouples interconnect and backend timing
- **Configurable Width:** Optional ID, DEST, USER signals (set width to 0 to disable)
- **Activity Monitoring:** Busy signal for power management

## Usage Example

```systemverilog
axis_slave #(
    .SKID_DEPTH(4),           // 16 entries
    .AXIS_DATA_WIDTH(64),
    .AXIS_ID_WIDTH(8),
    .AXIS_DEST_WIDTH(4),
    .AXIS_USER_WIDTH(1)
) u_axis_slave (
    .aclk(stream_clk),
    .aresetn(stream_resetn),

    // Slave interface (from network/interconnect)
    .s_axis_tdata(net_tdata),
    .s_axis_tstrb(net_tstrb),
    .s_axis_tlast(net_tlast),
    .s_axis_tid(net_tid),
    .s_axis_tdest(net_tdest),
    .s_axis_tuser(net_tuser),
    .s_axis_tvalid(net_tvalid),
    .s_axis_tready(net_tready),

    // Backend interface (to processing logic)
    .fub_axis_tdata(proc_tdata),
    .fub_axis_tstrb(proc_tstrb),
    .fub_axis_tlast(proc_tlast),
    .fub_axis_tid(proc_tid),
    .fub_axis_tdest(proc_tdest),
    .fub_axis_tuser(proc_tuser),
    .fub_axis_tvalid(proc_tvalid),
    .fub_axis_tready(proc_tready),

    .busy(slave_busy)
);
```

## Design Notes

- **Signal Flow:** Interconnect → Skid Buffer → Backend
- **Use Case:** Stream receivers, packet processors, video decoders
- **Buffering:** Allows backend to consume at its own pace without stalling interconnect

## Related Modules

- **[axis_master](axis_master.md)** - Stream master counterpart
- **[axis_slave_cg](axis_clock_gating_guide.md)** - Clock-gated version

---

**Last Updated:** 2025-10-20

## Navigation

- **[← Back to AXIS4 Index](README.md)**
- **[← Back to RTLAmba Index](../README.md)**
