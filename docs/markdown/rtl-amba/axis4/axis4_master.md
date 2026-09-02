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
> **Notation:** some examples below abbreviate a full port list as `.m_axis_*(name_*)` or
> `.fub_axis_*(iface.*)`. **This is shorthand for the reader, not legal SystemVerilog** — a
> port-name wildcard of that form does not compile. Expand it to explicit named connections
> (as in the "Basic Video Stream Processing" example) or use an interface port. The examples
> using this shorthand are illustrative of topology only and are not drop-in compilable.

### Basic Video Stream Processing

```systemverilog
axis4_master #(
    .SKID_DEPTH(4),           // 4-entry buffer
    .AXIS_DATA_WIDTH(64),     // 8 bytes per transfer
    .AXIS_ID_WIDTH(4),        // Support 16 streams
    .AXIS_DEST_WIDTH(4),      // Support 16 destinations
    .AXIS_USER_WIDTH(8)       // 8-bit control signals
) u_video_stream (
    .aclk            (video_clk),
    .aresetn         (video_resetn),

    // Input from video source
    .fub_axis_tdata    (pixel_data),
    .fub_axis_tstrb    (pixel_strb),
    .fub_axis_tlast    (line_end),
    .fub_axis_tid      (stream_id),
    .fub_axis_tdest    (display_id),
    .fub_axis_tuser    (pixel_ctrl),
    .fub_axis_tvalid   (pixel_valid),
    .fub_axis_tready   (pixel_ready),

    // Output to video pipeline
    .m_axis_tdata      (pipe_tdata),
    .m_axis_tstrb      (pipe_tstrb),
    .m_axis_tlast      (pipe_tlast),
    .m_axis_tid        (pipe_tid),
    .m_axis_tdest      (pipe_tdest),
    .m_axis_tuser      (pipe_tuser),
    .m_axis_tvalid     (pipe_tvalid),
    .m_axis_tready     (pipe_tready),

    .busy              (video_busy)
);
```

### Network Packet Processing

```systemverilog
// High-performance packet processing
axis4_master #(
    .SKID_DEPTH(8),           // 8-entry buffer (deepest legal) for latency tolerance
    .AXIS_DATA_WIDTH(512),    // 64 bytes per beat (512-bit)
    .AXIS_ID_WIDTH(8),        // 256 flow IDs
    .AXIS_DEST_WIDTH(6),      // 64 output ports
    .AXIS_USER_WIDTH(16)      // Packet metadata
) u_packet_master (
    .aclk            (net_clk),
    .aresetn         (net_resetn),

    // Input from packet classifier
    .fub_axis_tdata    (pkt_data),
    .fub_axis_tstrb    (pkt_keep),
    .fub_axis_tlast    (pkt_eop),
    .fub_axis_tid      (flow_id),
    .fub_axis_tdest    (output_port),
    .fub_axis_tuser    ({pkt_len, pkt_type}),
    .fub_axis_tvalid   (pkt_valid),
    .fub_axis_tready   (pkt_ready),

    // Output to switching fabric
    .m_axis_*(switch_axis_*),

    .busy              (pkt_proc_busy)
);
```

### DSP Data Pipeline

```systemverilog
// DSP processing chain with minimal sideband
axis4_master #(
    .SKID_DEPTH(2),           // 2-entry buffer (minimum latency)
    .AXIS_DATA_WIDTH(128),    // 4 x 32-bit samples
    .AXIS_ID_WIDTH(0),        // No stream ID needed
    .AXIS_DEST_WIDTH(0),      // No destination routing
    .AXIS_USER_WIDTH(4)       // Sample metadata
) u_dsp_stream (
    .aclk            (dsp_clk),
    .aresetn         (dsp_resetn),

    // Input from ADC interface
    .fub_axis_tdata    (adc_samples),
    .fub_axis_tstrb    (adc_valid_bytes),
    .fub_axis_tlast    (frame_end),
    .fub_axis_tid      (1'b0),          // Unused
    .fub_axis_tdest    (1'b0),          // Unused
    .fub_axis_tuser    (sample_metadata),
    .fub_axis_tvalid   (adc_valid),
    .fub_axis_tready   (adc_ready),

    // Output to DSP processing
    .m_axis_tdata      (proc_samples),
    .m_axis_tstrb      (proc_strb),
    .m_axis_tlast      (proc_frame_end),
    .m_axis_tid        (),              // Unconnected
    .m_axis_tdest      (),              // Unconnected
    .m_axis_tuser      (proc_metadata),
    .m_axis_tvalid     (proc_valid),
    .m_axis_tready     (proc_ready),

    .busy              (dsp_busy)
);
```

### Multi-Stream Router Integration

```systemverilog
module stream_router (
    input logic axi_clk,
    input logic axi_resetn,

    // Multiple input streams
    axi4s_if.slave  input_streams [4],
    // Single output stream
    axi4s_if.master output_stream
);

    // Stream masters for each input with buffering
    genvar i;
    generate
        for (i = 0; i < 4; i++) begin : gen_stream_masters
            axis4_master #(
                .SKID_DEPTH(4),
                .AXIS_DATA_WIDTH(64),
                .AXIS_ID_WIDTH(4),
                .AXIS_DEST_WIDTH(4),
                .AXIS_USER_WIDTH(1)
            ) u_stream_master (
                .aclk(axi_clk),
                .aresetn(axi_resetn),

                // Connect to input stream
                .fub_axis_*(input_streams[i].*),

                // Connect to arbiter
                .m_axis_*(arb_inputs[i].*),

                .busy(stream_busy[i])
            );
        end
    endgenerate

    // Stream arbiter for output selection
    axis_arbiter #(
        .NUM_INPUTS(4),
        .DATA_WIDTH(64)
    ) u_arbiter (
        .aclk(axi_clk),
        .aresetn(axi_resetn),
        .s_axis(arb_inputs),
        .m_axis(output_stream),
        .active_mask(stream_enable)
    );

endmodule
```

### Advanced Integration Patterns

#### Clock Domain Crossing

```systemverilog
// Cross clock domains with async FIFO
module axis_cdc_system (
    // Source domain
    input  logic        src_clk,
    input  logic        src_resetn,
    axi4s_if.slave      src_axis,

    // Destination domain
    input  logic        dst_clk,
    input  logic        dst_resetn,
    axi4s_if.master     dst_axis
);

    // Source domain buffering
    axis4_master #(
        .SKID_DEPTH(2),
        .AXIS_DATA_WIDTH(32),
        .AXIS_ID_WIDTH(4),
        .AXIS_DEST_WIDTH(4),
        .AXIS_USER_WIDTH(1)
    ) u_src_master (
        .aclk(src_clk),
        .aresetn(src_resetn),
        .fub_axis_*(src_axis.*),
        .m_axis_*(cdc_src_axis.*),
        .busy(src_busy)
    );

    // Async clock domain crossing.
    // gaxi_fifo_async.DEPTH is also a literal entry count (default 16).
    // DATA_WIDTH must equal the packed TSize of the stream being carried:
    //   TSize = DW + DW/8 + 1 + IW_WIDTH + DESTW_WIDTH + UW_WIDTH
    gaxi_fifo_async #(
        .DEPTH(64),                        // 64 entries
        .DATA_WIDTH(32 + 4 + 1 + 4 + 4 + 1)  // DW=32, SW=4, TLAST, TID=4, TDEST=4, TUSER=1
    ) u_cdc_fifo (
        .axi_wr_aclk(src_clk),
        .axi_wr_aresetn(src_resetn),
        .wr_valid(cdc_src_tvalid),
        .wr_ready(cdc_src_tready),
        .wr_data(cdc_src_packed),      // the packed TSize word, not a bundle

        .axi_rd_aclk(dst_clk),
        .axi_rd_aresetn(dst_resetn),
        .rd_valid(dst_tvalid),
        .rd_ready(dst_tready),
        .rd_data(dst_packed)
    );

endmodule
```

#### Stream Processing Pipeline

```systemverilog
// Multi-stage processing pipeline
module stream_pipeline (
    input logic clk, resetn,
    axi4s_if.slave  input_stream,
    axi4s_if.master output_stream
);

    // Pipeline stage interfaces
    axi4s_if stage1_out();
    axi4s_if stage2_out();
    axi4s_if stage3_out();

    // Stage 1: Input buffering
    axis4_master #(.SKID_DEPTH(2), .AXIS_DATA_WIDTH(64))
    u_stage1 (
        .aclk(clk), .aresetn(resetn),
        .fub_axis_*(input_stream.*),
        .m_axis_*(stage1_out.*),
        .busy(stage1_busy)
    );

    // Stage 2: Processing with buffering
    stream_processor u_processor (
        .clk(clk), .resetn(resetn),
        .s_axis(stage1_out), .m_axis(stage2_out)
    );

    axis4_master #(.SKID_DEPTH(4), .AXIS_DATA_WIDTH(64))
    u_stage2 (
        .aclk(clk), .aresetn(resetn),
        .fub_axis_*(stage2_out.*),
        .m_axis_*(stage3_out.*),
        .busy(stage2_busy)
    );

    // Stage 3: Output conditioning
    axis4_master #(.SKID_DEPTH(2), .AXIS_DATA_WIDTH(64))
    u_stage3 (
        .aclk(clk), .aresetn(resetn),
        .fub_axis_*(stage3_out.*),
        .m_axis_*(output_stream.*),
        .busy(stage3_busy)
    );

    assign pipeline_busy = stage1_busy | stage2_busy | stage3_busy;

endmodule
```

#### Clock Gating Integration

The clock-gated variant `axis4_master_cg` wraps this module and drives it from a gated clock.
Its control ports are `cfg_cg_enable` and `cfg_cg_idle_count`; its status ports are
`cg_gating` and `cg_idle`. There is **no `cg_enable`, no `cg_test_enable`, and no `busy`
output** on the `_cg` wrapper — the base module's `busy` is consumed internally as one of the
wakeup terms.

```systemverilog
// Clock gated version for power optimization
axis4_master_cg #(
    .SKID_DEPTH(4),
    .AXIS_DATA_WIDTH(64),
    .CG_IDLE_COUNT_WIDTH(4)
) u_cg_master (
    .aclk               (axi_clk),
    .aresetn            (axi_resetn),

    // Clock gating configuration
    .cfg_cg_enable      (stream_cg_enable),
    .cfg_cg_idle_count  (4'd8),

    // Standard AXI4-Stream interfaces (expand to explicit connections)
    // .fub_axis_tdata (...), ... , .m_axis_tready (...),

    // Clock gating status
    .cg_gating          (stream_clk_gated),
    .cg_idle            (stream_idle)
);

// System-level power management
always_ff @(posedge axi_clk) begin
    stream_power_down <= stream_idle && (idle_time > POWER_DOWN_DELAY);
end
```

See the [AXIS4 Clock-Gated Variants Guide](axis4_clock_gating_guide.md) for gating and
ungating behaviour, including the ungating latency and the `fub_axis_tready` hold-off while
gated.

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
