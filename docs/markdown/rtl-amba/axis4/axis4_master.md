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

# axis4_master

An AXI4-Stream master module that provides high-throughput streaming data transmission with configurable buffering and comprehensive support for all AXI4-Stream sideband signals including ID, DEST, and USER channels.

## Overview

The `axis4_master` module implements a complete AXI4-Stream master interface with integrated skid buffering for optimal streaming performance. It supports the full AXI4-Stream protocol with configurable data widths, optional sideband signals, and intelligent buffer management to maximize throughput in streaming data applications such as video processing, network packet handling, and DSP pipelines. In practice it's a shallow elastic buffer with an AXIS face on each side — which is exactly what you want between a producer and an interconnect that don't quite agree on timing.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| SKID_DEPTH | int | 4 | Skid buffer depth in **entries** (not a log2 exponent). Passed directly to `gaxi_skid_buffer.DEPTH`, which supports 2..8 inclusive |
| AXIS_DATA_WIDTH | int | 32 | AXI4-Stream data bus width in **bits** (must be a multiple of 8; `SW = AXIS_DATA_WIDTH/8`) |
| AXIS_ID_WIDTH | int | 8 | Stream ID width (0 to disable) |
| AXIS_DEST_WIDTH | int | 4 | Destination width (0 to disable) |
| AXIS_USER_WIDTH | int | 1 | User signal width (0 to disable) |

> **SKID_DEPTH is a literal entry count.** `SKID_DEPTH = 4` yields a 4-entry buffer, not 16.
> The underlying `gaxi_skid_buffer` is a shift-register FIFO whose `count` port is 4 bits wide;
> only the values 2..8 inclusive are supported. Any integer in that range is
> legal, odd values included -- `gaxi_skid_buffer` states "2..8 inclusive (any
> integer)" and guards it. The `{2,4,6,8}` restriction claimed here was an
> inference, not a contract.

## Ports

The full declaration, straight from the RTL:

```systemverilog
module axis4_master #(
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
    parameter int IW_WIDTH = (IW > 0) ? IW : 1,    // Minimum 1 bit for zero-width signals
    parameter int DESTW_WIDTH = (DESTW > 0) ? DESTW : 1,
    parameter int UW_WIDTH = (UW > 0) ? UW : 1,
    parameter int TSize    = DW+SW+1+IW_WIDTH+DESTW_WIDTH+UW_WIDTH  // Total packet size
) (
    // Global Clock and Reset
    input  logic                       aclk,
    input  logic                       aresetn,

    // Slave AXI4-Stream Interface (Input Side - FUB)
    input  logic [DW-1:0]              fub_axis_tdata,
    input  logic [SW-1:0]              fub_axis_tstrb,
    input  logic                       fub_axis_tlast,
    input  logic [IW_WIDTH-1:0]        fub_axis_tid,
    input  logic [DESTW_WIDTH-1:0]     fub_axis_tdest,
    input  logic [UW_WIDTH-1:0]        fub_axis_tuser,
    input  logic                       fub_axis_tvalid,
    output logic                       fub_axis_tready,

    // Master AXI4-Stream Interface (Output Side)
    output logic [DW-1:0]              m_axis_tdata,
    output logic [SW-1:0]              m_axis_tstrb,
    output logic                       m_axis_tlast,
    output logic [IW_WIDTH-1:0]        m_axis_tid,
    output logic [DESTW_WIDTH-1:0]     m_axis_tdest,
    output logic [UW_WIDTH-1:0]        m_axis_tuser,
    output logic                       m_axis_tvalid,
    input  logic                       m_axis_tready,

    // Status outputs for clock gating
    output logic                       busy
);
```

### Clock and Reset

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| aclk | 1 | Input | AXI4-Stream clock |
| aresetn | 1 | Input | AXI4-Stream active-low reset |

### Slave AXI4-Stream Interface (Input Side - FUB)

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| fub_axis_tdata | AXIS_DATA_WIDTH | Input | Stream data |
| fub_axis_tstrb | AXIS_DATA_WIDTH/8 | Input | Data byte strobes |
| fub_axis_tlast | 1 | Input | Last transfer in packet |
| fub_axis_tid | AXIS_ID_WIDTH | Input | Stream identifier |
| fub_axis_tdest | AXIS_DEST_WIDTH | Input | Destination routing |
| fub_axis_tuser | AXIS_USER_WIDTH | Input | User-defined sideband |
| fub_axis_tvalid | 1 | Input | Transfer valid |
| fub_axis_tready | 1 | Output | Transfer ready |

### Master AXI4-Stream Interface (Output Side)

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| m_axis_tdata | AXIS_DATA_WIDTH | Output | Stream data |
| m_axis_tstrb | AXIS_DATA_WIDTH/8 | Output | Data byte strobes |
| m_axis_tlast | 1 | Output | Last transfer in packet |
| m_axis_tid | AXIS_ID_WIDTH | Output | Stream identifier |
| m_axis_tdest | AXIS_DEST_WIDTH | Output | Destination routing |
| m_axis_tuser | AXIS_USER_WIDTH | Output | User-defined sideband |
| m_axis_tvalid | 1 | Output | Transfer valid |
| m_axis_tready | 1 | Input | Transfer ready |

### Status Interface

| Port | Width | Direction | Description |
|------|-------|-----------|-------------|
| busy | 1 | Output | Module activity indicator for clock gating |

## Functional Description

### Skid Buffer Design

The module employs a single GAXI skid buffer to manage streaming data flow:

1. **Input Buffering**: Incoming stream data buffered for flow control
2. **Packet Packing**: All stream signals packed into single buffer entry
3. **Flexible Unpacking**: Conditional unpacking based on enabled sideband signals

### Data Flow

```
FUB AXIS → Skid Buffer → Master AXIS → Downstream
     ↑           ↓               ↓
    Ready    Flow Control    Ready/Valid
```

### Key Features

- **AXI4-Stream Compliance**: Full protocol support including all optional signals
- **Flexible Configuration**: Zero-width support for unused sideband signals
- **Flow Control**: Skid buffer prevents pipeline stalls
- **Clock Gating Support**: Busy signal for power optimization
- **Packet Integrity**: TLAST preservation through buffering
- **Multi-Stream Support**: TID and TDEST routing capabilities

### Buffer Management

The skid buffer provides:
1. **Decoupling**: Separates upstream and downstream timing
2. **Flow Control**: Prevents data loss during backpressure
3. **Pipeline Optimization**: Eliminates ready-path combinatorial logic

### Conditional Signal Handling

The module uses generate blocks to handle various combinations of enabled/disabled sideband signals:

```systemverilog
// Example: Full signals enabled
if (IW > 0 && DESTW > 0 && UW > 0) begin
    // All sideband signals active
end else if (IW > 0 && DESTW == 0 && UW == 0) begin
    // Only TID active
end
// ... additional combinations
```

### Busy Signal Generation

Activity detection for clock gating:
```systemverilog
busy = (buffer_count > 0) || fub_axis_tvalid;
```

### Signal Description

#### Core Signals

| Signal | Width | Description |
|--------|-------|-------------|
| TDATA | 8-512 bits | Primary data payload |
| TSTRB | TDATA/8 bits | Byte lane strobes, one bit per byte lane |
| TVALID | 1 bit | Transfer valid indicator |
| TREADY | 1 bit | Transfer ready (backpressure) |
| TLAST | 1 bit | Last transfer in packet/frame |

#### TSTRB and TKEEP

ARM IHI 0051A defines two byte qualifiers: `TKEEP` (byte is part of the data stream) and
`TSTRB` (byte is a data byte rather than a position byte). This module implements **`TSTRB`
only** — there is no `TKEEP` port.

The buffer is byte-qualifier agnostic: `fub_axis_tstrb` is packed into the skid buffer entry
and reproduced on `m_axis_tstrb` unmodified, so it can equally carry a `TKEEP` mask if the
surrounding design treats it that way. Doing so is a naming convention on the integrator's
side, not protocol-compliant `TKEEP` support. See [Known Limitations](#known-limitations).

#### Optional Sideband Signals

| Signal | Width | Description |
|--------|-------|-------------|
| TID | 0-16 bits | Stream identifier for multiplexing |
| TDEST | 0-16 bits | Destination routing information |
| TUSER | 0-16 bits | User-defined control/status |

## Timing Characteristics
### Buffer Performance

| Characteristic | Value | Description |
|----------------|-------|-------------|
| Buffer Depth | 4 entries (default) | `SKID_DEPTH` entries, verbatim |
| Buffering Latency | 1 clock cycle | Input to output delay |
| Flow Control Latency | 1 clock cycle | Ready propagation |

`gaxi_skid_buffer` registers both `rd_valid` and the storage array, so the 1-cycle
input-to-output latency applies on **every** transfer, including the unstalled case. This is
not a bypass ("zero-bubble") skid buffer; there is no combinational path from
`fub_axis_tdata` to `m_axis_tdata`. Full throughput (one beat per cycle) is still sustained
once the pipeline is primed.

### Throughput Metrics

The figures below are **design targets for scoping purposes, not measured synthesis
results.** No target device, technology node, or timing report backs them. Treat them as
order-of-magnitude guidance and re-derive from your own synthesis run before committing to
a system budget.

| Metric | Indicative Value | Conditions |
|--------|------------------|------------|
| Maximum Frequency | 400-800 MHz | Technology dependent; unqualified by node |
| Peak Throughput | 3.2-25.6 GB/s | 64-bit to 512-bit at the frequencies above |
| Sustained Throughput | 95-99% of peak | With proper buffering |
| Pipeline Efficiency | >95% | Continuous data flow |

## Usage Examples

Every parameter and port below is read from the module declaration.

```systemverilog
axis4_master #(
    .SKID_DEPTH            (4),
    .AXIS_DATA_WIDTH       (32),
    .AXIS_ID_WIDTH         (8),
    .AXIS_DEST_WIDTH       (4),
    .AXIS_USER_WIDTH       (1)
) u_axis4_master (
    .aclk                  (aclk),
    .aresetn               (aresetn),
    .fub_axis_tdata        (fub_axis_tdata),
    .fub_axis_tstrb        (fub_axis_tstrb),
    .fub_axis_tlast        (fub_axis_tlast),
    .fub_axis_tid          (fub_axis_tid),
    .fub_axis_tdest        (fub_axis_tdest),
    .fub_axis_tuser        (fub_axis_tuser),
    .fub_axis_tvalid       (fub_axis_tvalid),
    .fub_axis_tready       (fub_axis_tready),
    .m_axis_tdata          (m_axis_tdata),
    .m_axis_tstrb          (m_axis_tstrb),
    .m_axis_tlast          (m_axis_tlast),
    .m_axis_tid            (m_axis_tid),
    .m_axis_tdest          (m_axis_tdest),
    .m_axis_tuser          (m_axis_tuser),
    .m_axis_tvalid         (m_axis_tvalid),
    .m_axis_tready         (m_axis_tready),
    .busy                  (busy)
);
```

## Design Notes

### Area Optimization
- Use minimum required data widths
- Disable unused sideband signals (set width to 0)
- Optimize buffer depths for application requirements
- Share buffers across multiple streams when possible

### Timing Optimization
- Register all interface outputs for timing closure
- Use appropriate buffer depths to break critical paths
- Consider pipeline stages for very high-frequency designs

### Power Optimization
- Use clock gating variant (`axis4_master_cg`) when available
- Implement activity-based power scaling
- Size buffers appropriately to minimize switching

### Known Limitations

| Limitation | Detail |
|------------|--------|
| No `TKEEP` | Only `TSTRB` is implemented. A protocol-compliant null-byte / position-byte distinction is not available. See [TSTRB and TKEEP](#tstrb-and-tkeep) |
| No `TWAKEUP` | The AXI4-Stream `TWAKEUP` low-power signal is not implemented |
| No native CDC | Both interfaces are on `aclk`. Crossing clock domains requires an external `gaxi_fifo_async` |
| No reordering or arbitration | The module is a single-stream elastic buffer. `TID`/`TDEST` are carried through unmodified; they are not decoded for routing |
| No protocol checking | The module does not detect or report `TVALID` deassertion before `TREADY`, or `TLAST` framing errors |
| `SKID_DEPTH` limited to 2..8 inclusive | The buffer is a timing element, not a rate adapter. Use a `gaxi_fifo_sync` downstream for deep elastic storage |

### Buffer Depth Selection

Choose buffer depths based on application characteristics:

Legal values are 2..8 inclusive entries. The skid buffer is a *timing* element, not a rate
adaptation FIFO — if an application needs tens or hundreds of entries of elastic storage,
place a `gaxi_fifo_sync` (or `gaxi_fifo_async` across clock domains) downstream rather than
attempting to scale `SKID_DEPTH`.

| Application Type | Recommended SKID_DEPTH | Buffer Size | Rationale |
|------------------|------------------------|-------------|-----------|
| Low Latency DSP | 2 | 2 entries | Reduce processing delay |
| Video Streaming | 4 | 4 entries | Absorb short backpressure bubbles |
| Network Packets | 6 | 6 entries | Tolerate bursty sink stalls |
| High Throughput | 8 | 8 entries | Maximum decoupling available |

### Data Width Optimization

```systemverilog
// Optimize data width for application
localparam VIDEO_PIXELS_PER_CYCLE = 4;
localparam PIXEL_BITS = 24;  // RGB888
localparam VIDEO_DATA_WIDTH = VIDEO_PIXELS_PER_CYCLE * PIXEL_BITS;

axis4_master #(
    .AXIS_DATA_WIDTH(VIDEO_DATA_WIDTH),  // 96 bits
    .SKID_DEPTH(4),
    .AXIS_USER_WIDTH(8)  // Control signals
) u_video_master (...);
```

### Sideband Signal Optimization

```systemverilog
// Minimize unused sideband signals for area/power
axis4_master #(
    .AXIS_DATA_WIDTH(128),
    .AXIS_ID_WIDTH(0),     // Disable TID
    .AXIS_DEST_WIDTH(0),   // Disable TDEST
    .AXIS_USER_WIDTH(4),   // Minimal TUSER
    .SKID_DEPTH(2)
) u_optimized_master (...);
```

## Related Modules

- **axis4_master_cg**: Clock-gated version for power optimization
- **axis4_slave**: Complementary AXI4-Stream slave implementation
- **gaxi_skid_buffer**: Underlying buffer infrastructure
- **gaxi_fifo_async**: Asynchronous FIFO for clock domain crossing

> The `axis_arbiter` and `axis_interconnect` blocks referenced in the "Multi-Stream Router
> Integration" example above are **not part of this repository**. That example illustrates a
> system topology built around `axis4_master`; the arbitration block is left to the
> integrator.

The `axis4_master` module provides a complete, high-performance solution for AXI4-Stream master functionality with advanced buffering, flexible signal configuration, and comprehensive system integration capabilities.

---

## Testing

`val/amba/test_axis4_master.py` exercises this module. It collects 14 parameter cases at the default `REG_LEVEL`.

```bash
source env_python
pytest val/amba/test_axis4_master.py -v
```

### What to Verify

**Protocol Compliance**
- Verify AXI4-Stream handshaking (VALID/READY)
- Check TLAST alignment with packet boundaries
- Validate sideband signal preservation

**Buffer Verification**
- Test buffer overflow/underflow protection
- Verify data integrity through buffering
- Check flow control under backpressure

**Performance Verification**
- Measure sustained throughput under various loads
- Verify buffer utilization efficiency
- Check latency characteristics

---

## Navigation

- **[← Back to axis4 index](../axis4/README.md)**
- **[← Back to rtl-amba index](../index.md)**
