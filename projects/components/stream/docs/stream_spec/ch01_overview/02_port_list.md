# STREAM Top-Level Port List

**Module:** `stream_core.sv`
**Location:** `projects/components/stream/rtl/macro/`
**Last Updated:** 2025-11-22

---

## Overview

This document provides a complete reference for all top-level ports of the STREAM Core module, organized by interface type. All port names, directions, widths, and descriptions are extracted directly from the RTL implementation.

**Quick Navigation:**
- [Clock and Reset](#clock-and-reset)
- [APB Programming Interface](#apb-programming-interface)
- [Configuration Interface](#configuration-interface)
- [Status Interface](#status-interface)
- [Performance Profiler Interface](#performance-profiler-interface)
- [AXI4 Master - Descriptor Fetch](#axi4-master---descriptor-fetch-256-bit)
- [AXI4 Master - Data Read](#axi4-master---data-read-parameterizable-width)
- [AXI4 Master - Data Write](#axi4-master---data-write-parameterizable-width)
- [Status/Debug Outputs](#statusdebug-outputs)
- [Unified Monitor Bus](#unified-monitor-bus-interface)

---

## Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock (100-500 MHz typical) |
| `rst_n` | input | 1 | Active-low asynchronous reset |

**Notes:**
- All STREAM logic operates in the `clk` domain
- Reset is asynchronous assert, synchronous deassert
- All registers use reset macros from `reset_defs.svh`

---

## APB Programming Interface

Per-channel descriptor kick-off interface. Each channel has independent valid/ready/address signals for descriptor chain start.

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `apb_valid[ch]` | input | NUM_CHANNELS | Channel descriptor address valid |
| `apb_ready[ch]` | output | NUM_CHANNELS | Channel ready to accept descriptor address |
| `apb_addr[ch]` | input | NUM_CHANNELS × ADDR_WIDTH | Descriptor address per channel (64-bit default) |

**Usage Pattern:**
```systemverilog
// Kick off channel 0 with descriptor at 0x1000_0000
apb_valid[0] = 1'b1;
apb_addr[0] = 64'h0000_0000_1000_0000;
// Wait for handshake
wait (apb_ready[0]);
apb_valid[0] = 1'b0;
```

**Notes:**
- Standard valid/ready handshake protocol
- Descriptor address must be aligned to descriptor size (32 bytes)
- Channel starts operation immediately after handshake
- Default: NUM_CHANNELS = 8, ADDR_WIDTH = 64

---

## Configuration Interface

### Per-Channel Configuration

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_channel_enable[ch]` | input | NUM_CHANNELS | Enable channel (0=disabled, 1=enabled) |
| `cfg_channel_reset[ch]` | input | NUM_CHANNELS | Soft reset channel (FSM → IDLE state) |

**Notes:**
- Channel must be enabled before accepting descriptors
- Soft reset clears channel FSM but preserves config

### Global Scheduler Configuration

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_sched_enable` | input | 1 | Global scheduler enable |
| `cfg_sched_timeout_cycles` | input | 16 | Timeout threshold (clock cycles) |
| `cfg_sched_timeout_enable` | input | 1 | Enable timeout detection |
| `cfg_sched_err_enable` | input | 1 | Enable error event reporting |
| `cfg_sched_compl_enable` | input | 1 | Enable completion event reporting |
| `cfg_sched_perf_enable` | input | 1 | Enable performance event reporting |

**Notes:**
- `cfg_sched_enable` is master enable for all schedulers
- Timeout measured from descriptor fetch to completion
- Event enables control MonBus traffic

### Descriptor Engine Configuration

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_desceng_enable` | input | 1 | Enable descriptor engine |
| `cfg_desceng_prefetch` | input | 1 | Enable descriptor prefetch |
| `cfg_desceng_fifo_thresh` | input | 4 | FIFO threshold for prefetch trigger |
| `cfg_desceng_addr0_base` | input | ADDR_WIDTH | Address range 0 base (protection) |
| `cfg_desceng_addr0_limit` | input | ADDR_WIDTH | Address range 0 limit (protection) |
| `cfg_desceng_addr1_base` | input | ADDR_WIDTH | Address range 1 base (protection) |
| `cfg_desceng_addr1_limit` | input | ADDR_WIDTH | Address range 1 limit (protection) |

**Notes:**
- Descriptor engine shared across all channels
- Prefetch improves latency for chained descriptors
- Address ranges provide optional descriptor memory protection

### AXI Monitor Configuration

Three identical sets of monitor config signals for descriptor, read, and write AXI masters:

| Signal Prefix | Applies To | Description |
|---------------|------------|-------------|
| `cfg_desc_mon_*` | Descriptor AXI | Descriptor fetch monitoring |
| `cfg_rdeng_mon_*` | Read AXI | Data read monitoring |
| `cfg_wreng_mon_*` | Write AXI | Data write monitoring |

Each monitor has the following configuration signals:

| Signal Suffix | Width | Description |
|---------------|-------|-------------|
| `_enable` | 1 | Enable monitor |
| `_err_enable` | 1 | Enable error packet reporting |
| `_perf_enable` | 1 | Enable performance packet reporting |
| `_timeout_enable` | 1 | Enable timeout detection |
| `_timeout_cycles` | 32 | Timeout threshold (cycles) |
| `_latency_thresh` | 32 | Latency threshold for events |
| `_pkt_mask` | 16 | Packet type mask (filter events) |
| `_err_select` | 4 | Error type selector |
| `_err_mask` | 8 | Error event mask |
| `_timeout_mask` | 8 | Timeout event mask |
| `_compl_mask` | 8 | Completion event mask |
| `_thresh_mask` | 8 | Threshold event mask |
| `_perf_mask` | 8 | Performance event mask |
| `_addr_mask` | 8 | Address event mask |
| `_debug_mask` | 8 | Debug event mask |

**Example Signals:**
```
cfg_desc_mon_enable          // Descriptor monitor enable
cfg_desc_mon_timeout_cycles  // Descriptor timeout threshold
cfg_rdeng_mon_err_enable     // Read engine error reporting enable
cfg_wreng_mon_perf_enable    // Write engine perf reporting enable
```

**Notes:**
- Monitors generate MonBus packets for events
- Masks control which event types are reported
- Timeout measured from AR/AW valid to last R/B response

### AXI Transfer Configuration

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_axi_rd_xfer_beats` | input | 8 | Read burst size (beats, 1-256) |
| `cfg_axi_wr_xfer_beats` | input | 8 | Write burst size (beats, 1-256) |

**Notes:**
- Configures AXI burst length for read/write engines
- Larger bursts improve bandwidth but increase latency
- Typical: 16 beats for DDR4, 8 beats for low-latency SRAM

### Performance Profiler Configuration

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_perf_enable` | input | 1 | Enable profiler |
| `cfg_perf_mode` | input | 1 | Profiler mode (0=timestamp, 1=elapsed) |
| `cfg_perf_clear` | input | 1 | Clear profiler counters and FIFO |

**Notes:**
- Timestamp mode: Records start/end timestamps (software calculates elapsed)
- Elapsed mode: Hardware calculates elapsed time directly
- Clear is a single-cycle pulse

---

## Status Interface

### Per-Channel Status

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `descriptor_engine_idle[ch]` | output | NUM_CHANNELS | Descriptor engine idle (no pending fetch) |
| `scheduler_idle[ch]` | output | NUM_CHANNELS | Scheduler in IDLE state (waiting for descriptor) |
| `scheduler_state[ch]` | output | NUM_CHANNELS × 7 | Scheduler FSM state (ONE-HOT encoding) |
| `sched_error[ch]` | output | NUM_CHANNELS | Scheduler error flag (sticky, cleared by reset) |
| `axi_rd_all_complete[ch]` | output | NUM_CHANNELS | All read transactions complete for channel |
| `axi_wr_all_complete[ch]` | output | NUM_CHANNELS | All write transactions complete for channel |

**Scheduler State Encoding (ONE-HOT):**
```systemverilog
7'b0000001  // CH_IDLE - Waiting for descriptor
7'b0000010  // CH_FETCH_DESC - Fetching descriptor
7'b0000100  // CH_XFER_DATA - Transfer in progress
7'b0001000  // CH_COMPLETE - Transfer complete
7'b0010000  // CH_NEXT_DESC - Chaining to next descriptor
7'b0100000  // CH_ERROR - Error occurred
7'b1000000  // (Reserved)
```

**Transfer Complete Condition:**
```systemverilog
channel_complete = scheduler_idle[ch] &&
                   axi_rd_all_complete[ch] &&
                   axi_wr_all_complete[ch];
```

---

## Performance Profiler Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `perf_fifo_empty` | output | 1 | Profiler FIFO empty flag |
| `perf_fifo_full` | output | 1 | Profiler FIFO full flag |
| `perf_fifo_count` | output | 16 | Profiler FIFO occupancy (0-256) |
| `perf_fifo_rd` | input | 1 | Read profiler entry (pop FIFO) |
| `perf_fifo_data_low` | output | 32 | Profiler data [31:0] (timestamp or elapsed) |
| `perf_fifo_data_high` | output | 32 | Profiler data [63:32] (metadata) |

**FIFO Entry Format:**

**Low Word [31:0]:**
- Timestamp mode: Timestamp in clock cycles
- Elapsed mode: Elapsed time in clock cycles

**High Word [31:0]:**
- Bits [31:4]: Reserved (0)
- Bit [3]: Event type (0=start, 1=end)
- Bits [2:0]: Channel ID (0-7)

**Read Sequence:**
```systemverilog
// Check FIFO not empty
if (!perf_fifo_empty) begin
    // Read 36-bit entry (two registers)
    perf_fifo_rd = 1'b1;  // Pulse to pop FIFO
    @(posedge clk);
    perf_fifo_rd = 1'b0;

    // Sample data on next cycle
    timestamp = perf_fifo_data_low;
    metadata = perf_fifo_data_high;
    channel_id = metadata[2:0];
    event_type = metadata[3];
end
```

---

## AXI4 Master - Descriptor Fetch (256-bit)

Fixed 256-bit width AXI4 master for descriptor fetch from memory.

### AR Channel (Read Address)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_desc_arid` | output | AXI_ID_WIDTH | Transaction ID |
| `m_axi_desc_araddr` | output | ADDR_WIDTH | Read address |
| `m_axi_desc_arlen` | output | 8 | Burst length - 1 (AXI encoding) |
| `m_axi_desc_arsize` | output | 3 | Burst size = log2(bytes per beat) |
| `m_axi_desc_arburst` | output | 2 | Burst type (01=INCR) |
| `m_axi_desc_arlock` | output | 1 | Lock type (0=normal) |
| `m_axi_desc_arcache` | output | 4 | Cache attributes |
| `m_axi_desc_arprot` | output | 3 | Protection attributes |
| `m_axi_desc_arqos` | output | 4 | QoS value |
| `m_axi_desc_arregion` | output | 4 | Region identifier |
| `m_axi_desc_aruser` | output | CHAN_WIDTH | User signal (channel ID) |
| `m_axi_desc_arvalid` | output | 1 | Address valid |
| `m_axi_desc_arready` | input | 1 | Address ready |

### R Channel (Read Data)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_desc_rid` | input | AXI_ID_WIDTH | Transaction ID |
| `m_axi_desc_rdata` | input | 256 | Read data (FIXED 256-bit descriptor) |
| `m_axi_desc_rresp` | input | 2 | Response (00=OKAY, 01=EXOKAY, 10=SLVERR, 11=DECERR) |
| `m_axi_desc_rlast` | input | 1 | Last beat of burst |
| `m_axi_desc_ruser` | input | CHAN_WIDTH | User signal (channel ID) |
| `m_axi_desc_rvalid` | input | 1 | Read data valid |
| `m_axi_desc_rready` | output | 1 | Read data ready |

**Notes:**
- Data width is FIXED at 256 bits (descriptor size)
- Typical burst: 1 beat (arlen=0) for single descriptor fetch
- arsize = 3'b101 (32 bytes = 2^5)
- ID encodes channel number for response routing

---

## AXI4 Master - Data Read (Parameterizable Width)

Parameterizable width AXI4 master for reading source data from memory. Default 512-bit.

### AR Channel (Read Address)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_rd_arid` | output | AXI_ID_WIDTH | Transaction ID |
| `m_axi_rd_araddr` | output | ADDR_WIDTH | Read address |
| `m_axi_rd_arlen` | output | 8 | Burst length - 1 |
| `m_axi_rd_arsize` | output | 3 | Burst size = log2(bytes per beat) |
| `m_axi_rd_arburst` | output | 2 | Burst type (01=INCR) |
| `m_axi_rd_arlock` | output | 1 | Lock type (0=normal) |
| `m_axi_rd_arcache` | output | 4 | Cache attributes |
| `m_axi_rd_arprot` | output | 3 | Protection attributes |
| `m_axi_rd_arqos` | output | 4 | QoS value |
| `m_axi_rd_arregion` | output | 4 | Region identifier |
| `m_axi_rd_aruser` | output | CHAN_WIDTH | User signal (channel ID) |
| `m_axi_rd_arvalid` | output | 1 | Address valid |
| `m_axi_rd_arready` | input | 1 | Address ready |

### R Channel (Read Data)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_rd_rid` | input | AXI_ID_WIDTH | Transaction ID |
| `m_axi_rd_rdata` | input | DATA_WIDTH | Read data (default 512-bit) |
| `m_axi_rd_rresp` | input | 2 | Response |
| `m_axi_rd_rlast` | input | 1 | Last beat of burst |
| `m_axi_rd_ruser` | input | CHAN_WIDTH | User signal (channel ID) |
| `m_axi_rd_rvalid` | input | 1 | Read data valid |
| `m_axi_rd_rready` | output | 1 | Read data ready |

**Notes:**
- Data width configurable via DATA_WIDTH parameter (default 512)
- Burst length configured via `cfg_axi_rd_xfer_beats` (default 16)
- arsize = log2(DATA_WIDTH/8) automatically calculated
- AXI skid buffers on external interface for timing closure

---

## AXI4 Master - Data Write (Parameterizable Width)

Parameterizable width AXI4 master for writing destination data to memory. Default 512-bit.

### AW Channel (Write Address)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_wr_awid` | output | AXI_ID_WIDTH | Transaction ID |
| `m_axi_wr_awaddr` | output | ADDR_WIDTH | Write address |
| `m_axi_wr_awlen` | output | 8 | Burst length - 1 |
| `m_axi_wr_awsize` | output | 3 | Burst size = log2(bytes per beat) |
| `m_axi_wr_awburst` | output | 2 | Burst type (01=INCR) |
| `m_axi_wr_awlock` | output | 1 | Lock type (0=normal) |
| `m_axi_wr_awcache` | output | 4 | Cache attributes |
| `m_axi_wr_awprot` | output | 3 | Protection attributes |
| `m_axi_wr_awqos` | output | 4 | QoS value |
| `m_axi_wr_awregion` | output | 4 | Region identifier |
| `m_axi_wr_awuser` | output | CHAN_WIDTH | User signal (channel ID) |
| `m_axi_wr_awvalid` | output | 1 | Address valid |
| `m_axi_wr_awready` | input | 1 | Address ready |

### W Channel (Write Data)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_wr_wdata` | output | DATA_WIDTH | Write data (default 512-bit) |
| `m_axi_wr_wstrb` | output | DATA_WIDTH/8 | Write strobes (byte enables, all 1s) |
| `m_axi_wr_wlast` | output | 1 | Last beat of burst |
| `m_axi_wr_wuser` | output | CHAN_WIDTH | User signal (channel ID) |
| `m_axi_wr_wvalid` | output | 1 | Write data valid |
| `m_axi_wr_wready` | input | 1 | Write data ready |

### B Channel (Write Response)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_wr_bid` | input | AXI_ID_WIDTH | Transaction ID |
| `m_axi_wr_bresp` | input | 2 | Response (00=OKAY, 01=EXOKAY, 10=SLVERR, 11=DECERR) |
| `m_axi_wr_buser` | input | CHAN_WIDTH | User signal (channel ID) |
| `m_axi_wr_bvalid` | input | 1 | Response valid |
| `m_axi_wr_bready` | output | 1 | Response ready |

**Notes:**
- Data width configurable via DATA_WIDTH parameter (default 512)
- Burst length configured via `cfg_axi_wr_xfer_beats` (default 16)
- awsize = log2(DATA_WIDTH/8) automatically calculated
- wstrb typically all 1s (full data width writes)
- AXI skid buffers on external interface for timing closure

---

## Status/Debug Outputs

### Descriptor AXI Monitor Status

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_sts_desc_mon_busy` | output | 1 | Monitor busy processing transaction |
| `cfg_sts_desc_mon_active_txns` | output | 8 | Active transaction count (0-255) |
| `cfg_sts_desc_mon_error_count` | output | 16 | Cumulative error count |
| `cfg_sts_desc_mon_txn_count` | output | 32 | Total transaction count |
| `cfg_sts_desc_mon_conflict_error` | output | 1 | ID conflict detected (sticky) |

### Read Engine AXI Monitor Status

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_sts_rdeng_skid_busy` | output | 1 | Skid buffer busy (not empty) |
| `cfg_sts_rdeng_mon_active_txns` | output | 8 | Active transaction count |
| `cfg_sts_rdeng_mon_error_count` | output | 16 | Cumulative error count |
| `cfg_sts_rdeng_mon_txn_count` | output | 32 | Total transaction count |
| `cfg_sts_rdeng_mon_conflict_error` | output | 1 | ID conflict detected (sticky) |

### Write Engine AXI Monitor Status

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_sts_wreng_skid_busy` | output | 1 | Skid buffer busy (not empty) |
| `cfg_sts_wreng_mon_active_txns` | output | 8 | Active transaction count |
| `cfg_sts_wreng_mon_error_count` | output | 16 | Cumulative error count |
| `cfg_sts_wreng_mon_txn_count` | output | 32 | Total transaction count |
| `cfg_sts_wreng_mon_conflict_error` | output | 1 | ID conflict detected (sticky) |

**Notes:**
- Status signals for debug and performance analysis
- Transaction counts never roll over (use for profiling)
- Error counts increment on any AXI error response
- ID conflicts indicate internal RTL bug (should never occur)

---

## Unified Monitor Bus Interface

Single output interface for all STREAM monitoring events.

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `mon_valid` | output | 1 | Monitor packet valid |
| `mon_ready` | input | 1 | Monitor packet ready (from downstream consumer) |
| `mon_packet` | output | 64 | Monitor packet data (64-bit standard format) |

**MonBus Packet Format (64-bit):**
```
[63:56] - Packet type (event code)
[55:48] - Agent ID (source identifier)
[47:40] - Unit ID (1 for STREAM)
[39:32] - Channel ID (0-7)
[31:0]  - Event-specific data
```

**MonBus Sources:**
- Descriptor engines: 8 sources, agent IDs 16-23 (0x10-0x17)
- Schedulers: 8 sources, agent IDs 48-55 (0x30-0x37)
- Descriptor AXI monitor: agent ID 8 (0x08)
- Read AXI monitor: configurable agent ID
- Write AXI monitor: configurable agent ID

**Downstream Integration:**
```systemverilog
// Connect to MonBus FIFO for buffering
gaxi_fifo_sync #(
    .DATA_WIDTH(64),
    .DEPTH(256)
) u_mon_fifo (
    .i_clk    (clk),
    .i_rst_n  (rst_n),
    .i_data   (mon_packet),
    .i_valid  (mon_valid),
    .o_ready  (mon_ready),
    // ... downstream connection
);
```

**Notes:**
- Standard AMBA monitor bus protocol
- Always buffer with FIFO to prevent backpressure to STREAM
- Packet format documented in `rtl/amba/includes/monitor_pkg.sv`
- Event codes defined in STREAM package

---

## Port Count Summary

| Interface Type | Input Ports | Output Ports | Bidirectional |
|----------------|-------------|--------------|---------------|
| Clock/Reset | 2 | 0 | 0 |
| APB Programming | NUM_CHANNELS × (1 + ADDR_WIDTH) | NUM_CHANNELS | 0 |
| Configuration | ~150 | 0 | 0 |
| Status | 1 (perf_fifo_rd) | NUM_CHANNELS × 10 + 30 | 0 |
| Perf Profiler | 1 | 4 | 0 |
| AXI Desc Master | 7 | 14 | 0 |
| AXI Read Master | 7 | 14 | 0 |
| AXI Write Master | 10 | 19 | 0 |
| MonBus | 1 | 2 | 0 |

**Approximate Total:** ~350 ports (varies with NUM_CHANNELS and ADDR_WIDTH/DATA_WIDTH)

---

## Default Parameter Values

| Parameter | Default | Description |
|-----------|---------|-------------|
| `NUM_CHANNELS` | 8 | Number of DMA channels |
| `CHAN_WIDTH` | 3 | Channel ID width (log2(NUM_CHANNELS)) |
| `ADDR_WIDTH` | 64 | Address bus width |
| `DATA_WIDTH` | 512 | Data bus width |
| `AXI_ID_WIDTH` | 8 | AXI transaction ID width |
| `FIFO_DEPTH` | 512 | Per-channel FIFO depth |
| `AR_MAX_OUTSTANDING` | 8 | Max concurrent read requests |
| `AW_MAX_OUTSTANDING` | 8 | Max concurrent write requests |

---

## Related Documentation

- **[Stream Core Block Spec](../ch02_blocks/01_stream_core.md)** - Detailed block documentation
- **[Clocks and Reset](03_clocks_and_reset.md)** - Timing specifications
- **[Architecture](01_architecture.md)** - System architecture overview

---

**Last Updated:** 2025-11-22
**Maintained By:** STREAM Architecture Team
