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

# AXIS4 (AXI4-Stream) Modules

**Location:** `rtl/amba/axis4/`
**Test Location:** `val/amba/`
**Status:** ✅ Production Ready

---

## Overview

The AXIS4 subsystem provides a complete implementation of the ARM AMBA AXI4-Stream protocol—a high-performance streaming interface optimized for unidirectional data flows such as video processing, network packet handling, and DSP pipelines.

### Key Features

- ✅ **AXI4-Stream Protocol:** Streaming-optimized subset (no address channels)
- ✅ **High Throughput:** Up to 25.6 GB/s (512-bit @ 400 MHz)
- ✅ **Flexible Sideband Signals:** TID, TDEST, TUSER for routing/control
- ✅ **Packet Framing:** TLAST for packet/frame boundaries
- ✅ **Elastic Buffering:** Integrated skid buffers for timing closure
- ✅ **Clock Gating Variants:** Power-optimized versions
- ✅ **Typical Use:** Video streams, network packets, DSP pipelines

---

## Module Categories

### Core Master/Slave Modules

| Module | Description | Documentation | Status |
|--------|-------------|---------------|--------|
| **axis_master** | AXIS master with buffered output | [axis_master.md](axis_master.md) | ✅ Documented |
| **axis_slave** | AXIS slave with buffered input | [axis_slave.md](axis_slave.md) | ✅ Documented |

### Clock-Gated Variants

**All clock-gated variants documented in:** [axis_clock_gating_guide.md](axis_clock_gating_guide.md)

| Module | Base Module | Status |
|--------|-------------|--------|
| **axis_master_cg** | [axis_master](axis_master.md) | ✅ Documented |
| **axis_slave_cg** | [axis_slave](axis_slave.md) | ✅ Documented |

---

## AXI4-Stream Protocol Overview

### Streaming vs Memory-Mapped

| Feature | AXI4 | AXI4-Stream |
|---------|------|-------------|
| **Address Channels** | AW/AR (5 channels) | None (streaming) |
| **Data Flow** | Bidirectional | Unidirectional |
| **Transaction Type** | Memory-mapped | Data streaming |
| **Backpressure** | Via ready signals | Via TREADY |
| **Packet Framing** | Not applicable | TLAST signal |
| **Routing** | Address-based | TID/TDEST-based |
| **Typical Use** | Register/memory access | Video/network/DSP |

### Signal Architecture

AXI4-Stream uses a single channel for streaming data:

**Core Signals:**
- **TDATA** - Streaming data payload (8-512 bits)
- **TSTRB** - Byte lane strobes (1 bit per byte)
- **TVALID** - Data valid indicator
- **TREADY** - Ready for data (backpressure)
- **TLAST** - Last transfer in packet/frame

**Optional Sideband Signals:**
- **TID** - Stream identifier (multiplexing)
- **TDEST** - Destination routing
- **TUSER** - User-defined control/status

### Key Signals

**Data Transfer:**
- `TDATA[N:0]` - Primary streaming data
- `TSTRB[N/8:0]` - Byte valid indicators (1=valid byte)
- `TVALID` - Transfer valid
- `TREADY` - Transfer ready

**Packet Control:**
- `TLAST` - End of packet/frame marker

**Routing/Control:**
- `TID[N:0]` - Stream ID for multiplexing (optional)
- `TDEST[N:0]` - Destination routing information (optional)
- `TUSER[N:0]` - User-defined metadata (optional)

---

## Quick Start

### Basic Stream Master

```systemverilog
axis_master #(
    .SKID_DEPTH(4),           // 16 entries
    .AXIS_DATA_WIDTH(64),     // 8 bytes per transfer
    .AXIS_ID_WIDTH(4),        // 16 streams
    .AXIS_DEST_WIDTH(4),      // 16 destinations
    .AXIS_USER_WIDTH(8)       // 8-bit control
) u_stream_master (
    .aclk               (stream_clk),
    .aresetn            (stream_resetn),

    // Frontend interface (from source)
    .fub_axis_tdata     (src_tdata),
    .fub_axis_tstrb     (src_tstrb),
    .fub_axis_tlast     (src_tlast),
    .fub_axis_tid       (src_tid),
    .fub_axis_tdest     (src_tdest),
    .fub_axis_tuser     (src_tuser),
    .fub_axis_tvalid    (src_tvalid),
    .fub_axis_tready    (src_tready),

    // Master interface (to interconnect)
    .m_axis_tdata       (net_tdata),
    // ... rest of master signals

    .busy               (master_busy)
);
```

### Basic Stream Slave

```systemverilog
axis_slave #(
    .SKID_DEPTH(4),           // 16 entries
    .AXIS_DATA_WIDTH(64),
    .AXIS_ID_WIDTH(8),
    .AXIS_DEST_WIDTH(4),
    .AXIS_USER_WIDTH(1)
) u_stream_slave (
    .aclk               (stream_clk),
    .aresetn            (stream_resetn),

    // Slave interface (from interconnect)
    .s_axis_tdata       (net_tdata),
    .s_axis_tstrb       (net_tstrb),
    .s_axis_tlast       (net_tlast),
    .s_axis_tid         (net_tid),
    .s_axis_tdest       (net_tdest),
    .s_axis_tuser       (net_tuser),
    .s_axis_tvalid      (net_tvalid),
    .s_axis_tready      (net_tready),

    // Backend interface (to processor)
    .fub_axis_tdata     (proc_tdata),
    // ... rest of backend signals

    .busy               (slave_busy)
);
```

### Video Processing Pipeline

```systemverilog
// Video frame buffer with packet boundaries
axis_master #(
    .SKID_DEPTH(5),           // 32-entry buffer
    .AXIS_DATA_WIDTH(96),     // 4 pixels x 24-bit RGB
    .AXIS_ID_WIDTH(0),        // No stream ID
    .AXIS_DEST_WIDTH(4),      // 16 display outputs
    .AXIS_USER_WIDTH(16)      // Frame/line metadata
) u_video_master (
    .aclk               (pixel_clk),
    .aresetn            (video_resetn),

    // From frame buffer
    .fub_axis_tdata     (pixel_data),      // RGB pixel data
    .fub_axis_tstrb     (pixel_strb),      // Valid bytes
    .fub_axis_tlast     (line_end),        // End of video line
    .fub_axis_tid       (1'b0),            // Unused
    .fub_axis_tdest     (display_id),      // Target display
    .fub_axis_tuser     ({frame_num, line_num}),
    .fub_axis_tvalid    (pixel_valid),
    .fub_axis_tready    (pixel_ready),

    // To video processing chain
    .m_axis_tdata       (proc_pixel_data),
    .m_axis_tstrb       (proc_pixel_strb),
    .m_axis_tlast       (proc_line_end),
    .m_axis_tid         (),
    .m_axis_tdest       (proc_display_id),
    .m_axis_tuser       (proc_metadata),
    .m_axis_tvalid      (proc_valid),
    .m_axis_tready      (proc_ready),

    .busy               (video_busy)
);
```

### Network Packet Processing

```systemverilog
// High-bandwidth packet processing
axis_slave #(
    .SKID_DEPTH(6),           // 64-entry buffer for latency
    .AXIS_DATA_WIDTH(512),    // 64 bytes per beat
    .AXIS_ID_WIDTH(8),        // 256 flow IDs
    .AXIS_DEST_WIDTH(6),      // 64 output ports
    .AXIS_USER_WIDTH(16)      // Packet metadata
) u_packet_slave (
    .aclk               (net_clk),
    .aresetn            (net_resetn),

    // From network interface
    .s_axis_tdata       (rx_pkt_data),
    .s_axis_tstrb       (rx_pkt_keep),     // Byte valid
    .s_axis_tlast       (rx_pkt_eop),      // End of packet
    .s_axis_tid         (rx_flow_id),
    .s_axis_tdest       (rx_output_port),
    .s_axis_tuser       ({pkt_len, pkt_type}),
    .s_axis_tvalid      (rx_pkt_valid),
    .s_axis_tready      (rx_pkt_ready),

    // To packet processor
    .fub_axis_tdata     (proc_pkt_data),
    .fub_axis_tstrb     (proc_pkt_keep),
    .fub_axis_tlast     (proc_pkt_eop),
    .fub_axis_tid       (proc_flow_id),
    .fub_axis_tdest     (proc_port),
    .fub_axis_tuser     (proc_metadata),
    .fub_axis_tvalid    (proc_pkt_valid),
    .fub_axis_tready    (proc_pkt_ready),

    .busy               (packet_busy)
);
```

---

## Testing

All AXIS4 modules are verified using CocoTB-based testbenches:

```bash
# Run all AXIS4 tests
pytest val/amba/test_axis*.py -v

# Run specific module tests
pytest val/amba/test_axis_master.py -v
pytest val/amba/test_axis_slave.py -v

# Run clock-gated variant tests
pytest val/amba/test_axis_master_cg.py -v
pytest val/amba/test_axis_slave_cg.py -v

# Run with waveforms
pytest val/amba/test_axis_master.py --vcd=waves.vcd -v
```

---

## Design Patterns

### Pattern 1: Elastic Buffering

All core modules use `gaxi_skid_buffer`:
- Decouples source and sink timing
- Configurable depth per module
- 1-cycle latency overhead
- Full backpressure handling

### Pattern 2: Packet Framing

TLAST signal marks packet boundaries:
```systemverilog
// Video: TLAST marks end of line
tlast = (pixel_count == PIXELS_PER_LINE - 1);

// Network: TLAST marks end of packet
tlast = (byte_count == packet_length - 1);

// DSP: TLAST marks end of frame
tlast = (sample_count == FRAME_SIZE - 1);
```

### Pattern 3: Stream Multiplexing

TID enables multiple logical streams:
```systemverilog
// Four video streams on single physical interface
.fub_axis_tid(camera_id),  // 0-3 for 4 cameras
.fub_axis_tdest(display_id) // Route to specific display
```

### Pattern 4: Clock Gating

Clock-gated variants (`*_cg`) add power management:
- Dynamic gating based on busy signal
- Configurable idle threshold
- 0-cycle ungating latency
- Best for packet-based streams with idle gaps

---

## Performance Characteristics

### Throughput

| Configuration | Bandwidth | Notes |
|--------------|-----------|-------|
| 32-bit @ 400 MHz | 1.6 GB/s | Typical DSP |
| 64-bit @ 400 MHz | 3.2 GB/s | Video processing |
| 128-bit @ 400 MHz | 6.4 GB/s | High-bandwidth video |
| 512-bit @ 400 MHz | 25.6 GB/s | Network/storage |

### Latency

| Path | Cycles | Notes |
|------|--------|-------|
| Buffer latency | 1 | Skid buffer overhead |
| Master → Slave | 2-3 | Through interconnect |
| Typical pipeline | 5-10 | Multi-stage processing |

### Resource Usage

| Module Type | LUTs | FFs | BRAM | Notes |
|-------------|------|-----|------|-------|
| Master/Slave (64-bit) | ~150 | ~100 | 0 | Base module |
| Clock-gated (+cg) | +50 | +30 | 0 | Clock gating logic |
| Wider data (512-bit) | ~400 | ~350 | 0 | 8x data width |

**vs AXI4:** ~60-70% resource savings (no address channels, simpler protocol)

---

## Common Use Cases

### Video Processing

**Characteristics:**
- High throughput (1-10 GB/s)
- Regular packet structure (lines/frames)
- TLAST marks line/frame boundaries
- TUSER carries frame metadata

**Recommended Configuration:**
```systemverilog
.AXIS_DATA_WIDTH(64-128),  // Multiple pixels per cycle
.SKID_DEPTH(4-5),          // 16-32 entry buffer
.AXIS_USER_WIDTH(8-16)     // Frame/line metadata
```

### Network Packet Processing

**Characteristics:**
- Variable packet sizes
- High packet rate
- TID for flow identification
- TDEST for output routing

**Recommended Configuration:**
```systemverilog
.AXIS_DATA_WIDTH(256-512), // Wide data bus
.SKID_DEPTH(5-6),          // 32-64 entry buffer
.AXIS_ID_WIDTH(8),         // 256 flows
.AXIS_DEST_WIDTH(6)        // 64 ports
```

### DSP Pipelines

**Characteristics:**
- Continuous data flow
- Fixed sample rate
- Minimal sideband signals
- Low latency requirements

**Recommended Configuration:**
```systemverilog
.AXIS_DATA_WIDTH(32-128),  // Sample data
.SKID_DEPTH(2-3),          // Minimal buffer
.AXIS_ID_WIDTH(0),         // No multiplexing
.AXIS_DEST_WIDTH(0),       // No routing
.AXIS_USER_WIDTH(4)        // Minimal metadata
```

---

## Parameter Selection Guidelines

### Data Width (AXIS_DATA_WIDTH)

| Application | Recommended Width | Rationale |
|-------------|-------------------|-----------|
| Audio processing | 32-64 bits | 1-2 samples per cycle |
| SD video | 64-96 bits | 2-4 pixels per cycle |
| HD video | 128-256 bits | Multiple pixels per cycle |
| 4K video | 256-512 bits | High pixel throughput |
| Network (1G) | 64-128 bits | Moderate packet rate |
| Network (10G/100G) | 256-512 bits | High packet rate |

### Buffer Depth (SKID_DEPTH)

| SKID_DEPTH | Buffer Size | Use Case |
|------------|-------------|----------|
| 2 | 4 entries | Low latency, continuous streams |
| 3 | 8 entries | Typical DSP pipelines |
| 4 | 16 entries | Video processing (default) |
| 5 | 32 entries | Network packets, variable latency |
| 6 | 64 entries | High-latency tolerance |

### Sideband Signal Widths

**TID (Stream ID):**
- 0: Single stream, no multiplexing
- 4: Up to 16 concurrent streams
- 8: Up to 256 concurrent streams

**TDEST (Destination):**
- 0: No routing (point-to-point)
- 4: Up to 16 destinations
- 6: Up to 64 destinations (network)

**TUSER (User Metadata):**
- 0-1: Minimal or no metadata
- 4-8: Frame/packet control
- 16+: Complex metadata

---

## Related Documentation

### Protocol Specifications
- ARM IHI 0051A: AMBA AXI4-Stream Protocol Specification

### RTL Design Sherpa Documentation
- **[RTLAmba Overview](../overview.md)** - Complete AMBA subsystem architecture
- **[AXI4 Modules](../axi4/README.md)** - Memory-mapped protocol (comparison)
- **[AXIL4 Modules](../axil4/README.md)** - Simplified control interface
- **[GAXI Modules](../gaxi/README.md)** - Generic AXI utilities (buffers, FIFOs)

### Source Code
- RTL: `rtl/amba/axis4/`
- Tests: `val/amba/test_axis*.py`
- Framework: `bin/CocoTBFramework/components/axis4/`
- Shared Infrastructure: `rtl/amba/shared/` (gaxi_skid_buffer)

---

## Design Notes

### When to Use AXI4-Stream

**✅ Use AXI4-Stream For:**
- Video/image processing pipelines
- Network packet processing
- DSP data flows
- High-throughput unidirectional data
- Streaming accelerators

**❌ Use AXI4 For:**
- Memory-mapped register access
- Random access patterns
- Bidirectional data flows
- Address-based routing

### Buffer Depth Trade-offs

**Shallow Buffers (SKID_DEPTH = 2-3):**
- ✅ Lower latency
- ✅ Smaller area
- ❌ Less tolerance for backpressure
- **Use for:** Low-latency DSP, continuous streams

**Deep Buffers (SKID_DEPTH = 5-6):**
- ✅ High backpressure tolerance
- ✅ Better throughput under variable load
- ❌ Higher latency
- ❌ Larger area
- **Use for:** Network packets, variable-latency paths

### Sideband Signal Optimization

**Minimize unused signals for area/power:**
```systemverilog
// Video processing - no routing needed
.AXIS_ID_WIDTH(0),     // No stream multiplexing
.AXIS_DEST_WIDTH(0),   // No destination routing
.AXIS_USER_WIDTH(8)    // Only frame metadata

// vs Network processing - full routing
.AXIS_ID_WIDTH(8),     // 256 flows
.AXIS_DEST_WIDTH(6),   // 64 ports
.AXIS_USER_WIDTH(16)   // Full packet metadata
```

---

**Last Updated:** 2025-10-20

---

## Navigation

- **[← Back to RTLAmba Index](../README.md)**
- **[← Back to Main Documentation Index](../../index.md)**
