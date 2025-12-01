# AXI Read Engine

**Module:** `axi_read_engine.sv`
**Location:** `projects/components/stream/rtl/fub/`
**Category:** FUB (Functional Unit Block)
**Parent:** `stream_core.sv`
**Status:** Implemented
**Last Updated:** 2025-11-30

---

## Overview

The `axi_read_engine` module is a high-performance multi-channel AXI4 read engine with space-aware arbitration. It serves all 8 STREAM channels through a single AXI master interface with intelligent flow control.

### Key Features

- **Round-Robin Arbitration:** Fair scheduling across channels
- **Space-Aware Masking:** Only arbitrate channels with sufficient SRAM space
- **Pre-Allocation Handshake:** Reserve SRAM space before data arrives
- **Streaming Data Path:** Direct passthrough to SRAM controller
- **Channel ID in AXI ID:** Enables per-channel response routing
- **Pipelined/Non-Pipelined Modes:** Configurable outstanding transaction depth

---

## Architecture

### Operation Flow

```
1. Scheduler Interface: Each channel can request read bursts
2. Space Checking: Mask channels without sufficient SRAM space
3. Arbitration: Round-robin arbiter selects next channel to service
4. AXI AR Issue: Issue read command to AXI, assert rd_alloc to SRAM controller
5. AXI R Response: Stream read data directly to SRAM controller
```

### Key Design Decisions

**Combinational AR Outputs:**
AR outputs are driven combinationally from the arbiter to avoid 1-cycle delay. When `axi_rd_alloc_space_free` goes to 0, `arvalid` drops in the same cycle.

**No Internal Buffering:**
The engine is a streaming pipeline with no internal data storage. Data flows directly from AXI R channel to SRAM controller.

### System Idle Behavior

When ALL channels complete their work (`w_arb_request == 0`), the engine becomes idle until new requests arrive. This is NOT a bubble - it's legitimate system idle.

**Why This Matters for Testing:**
- With few active channels and short bursts, there are brief periods when all channels are in their WRITE phase
- During these periods, `m_axi_arvalid = 0` (no R channel activity)
- This is EXPECTED behavior, not a performance bug
- The `dbg_arb_request` signal exposes `w_arb_request` to help testbenches distinguish:
  - **TRUE BUBBLE:** arvalid=0 while arb_request!=0 (channels waiting, arbiter stalled)
  - **SYSTEM IDLE:** arvalid=0 while arb_request==0 (no channels need service)

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `NUM_CHANNELS` | int | 8 | Number of channels |
| `ADDR_WIDTH` | int | 64 | AXI address width |
| `DATA_WIDTH` | int | 512 | AXI data width |
| `ID_WIDTH` | int | 8 | AXI ID width |
| `SEG_COUNT_WIDTH` | int | 8 | Width of space/count signals |
| `PIPELINE` | int | 0 | 0: non-pipelined, 1: pipelined |
| `AR_MAX_OUTSTANDING` | int | 8 | Maximum outstanding AR requests (PIPELINE=1) |
| `STROBE_EVERY_BEAT` | int | 0 | 0: strobe on last beat, 1: strobe every beat |

### Derived Parameters

| Parameter | Derivation | Description |
|-----------|------------|-------------|
| `NC` | NUM_CHANNELS | Short alias |
| `AW` | ADDR_WIDTH | Short alias |
| `DW` | DATA_WIDTH | Short alias |
| `IW` | ID_WIDTH | Short alias |
| `SCW` | SEG_COUNT_WIDTH | Segment count width |
| `CIW` | $clog2(NC) | Channel ID width (min 1 bit) |

---

## Port List

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `clk` | input | 1 | System clock |
| `rst_n` | input | 1 | Active-low asynchronous reset |

### Configuration Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cfg_axi_rd_xfer_beats` | input | 8 | Transfer size in beats (all channels) |

### Scheduler Interface (Per-Channel)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `sched_rd_valid[ch]` | input | NC | Channel requests read |
| `sched_rd_addr[ch]` | input | NC x AW | Source addresses |
| `sched_rd_beats[ch]` | input | NC x 32 | Beats remaining to read |

### Completion Interface (Per-Channel)

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `sched_rd_done_strobe[ch]` | output | NC | Burst completed (1 cycle pulse) |
| `sched_rd_beats_done[ch]` | output | NC x 32 | Number of beats completed |

### SRAM Allocation Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `axi_rd_alloc_req` | output | 1 | Request space allocation |
| `axi_rd_alloc_size` | output | 8 | Beats to reserve |
| `axi_rd_alloc_id` | output | IW | Transaction ID (channel) |
| `axi_rd_alloc_space_free[ch]` | input | NC x SCW | Free space per channel |

### SRAM Write Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `axi_rd_sram_valid` | output | 1 | Read data valid |
| `axi_rd_sram_ready` | input | 1 | Ready to accept data |
| `axi_rd_sram_id` | output | IW | Transaction ID (channel) |
| `axi_rd_sram_data` | output | DW | Read data payload |

### AXI4 AR Channel

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_arvalid` | output | 1 | Address valid |
| `m_axi_arready` | input | 1 | Address ready |
| `m_axi_arid` | output | IW | Transaction ID |
| `m_axi_araddr` | output | AW | Address |
| `m_axi_arlen` | output | 8 | Burst length - 1 |
| `m_axi_arsize` | output | 3 | Burst size (log2 bytes) |
| `m_axi_arburst` | output | 2 | Burst type (INCR) |

### AXI4 R Channel

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_rvalid` | input | 1 | Read data valid |
| `m_axi_rready` | output | 1 | Read data ready |
| `m_axi_rid` | input | IW | Transaction ID |
| `m_axi_rdata` | input | DW | Read data |
| `m_axi_rresp` | input | 2 | Response |
| `m_axi_rlast` | input | 1 | Last beat of burst |

### Error Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `sched_rd_error[ch]` | output | NC | Sticky error flag per channel |

### Debug Interface

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `dbg_rd_all_complete[ch]` | output | NC | All reads complete |
| `dbg_r_beats_rcvd` | output | 32 | Total R beats received |
| `dbg_sram_writes` | output | 32 | Total writes to SRAM |
| `dbg_arb_request[ch]` | output | NC | Arbiter request vector |

---

## Operation

### Space-Aware Request Masking

```systemverilog
// Only request arbitration if:
// 1. Scheduler is requesting (sched_rd_valid)
// 2. Sufficient SRAM space available (w_space_ok)
// 3. Below outstanding limit (w_below_outstanding_limit)
w_arb_request[i] = sched_rd_valid[i] && w_space_ok[i] && w_below_outstanding_limit[i];
```

### Transfer Size Calculation

```systemverilog
// Calculate actual transfer size for this channel
// Min of remaining beats or configured max
w_transfer_size[i] = (sched_rd_beats[i] <= cfg_axi_rd_xfer_beats + 1) ?
                     (sched_rd_beats[i] - 1) : cfg_axi_rd_xfer_beats;
```

### Outstanding Transaction Tracking

**PIPELINE=0 (Non-Pipelined):**
- Binary flag per channel (0 or 1 outstanding)
- Set when AR issues for channel
- Clear when R last arrives for channel

**PIPELINE=1 (Pipelined):**
- Counter per channel (0 to AR_MAX_OUTSTANDING)
- Increment on AR handshake
- Decrement on R last handshake

### Completion Strobe

Strobes fire when AR transaction is accepted (not when R completes):
```systemverilog
// Pulse when AR transaction is accepted (arvalid && arready)
// This tells scheduler that request was issued to AXI bus
if (m_axi_arvalid && m_axi_arready) begin
    r_done_strobe[w_arb_grant_id] <= 1'b1;
    r_beats_done[w_arb_grant_id] <= w_transfer_size[w_arb_grant_id] + 1;
end
```

---

## Integration Example

```systemverilog
axi_read_engine #(
    .NUM_CHANNELS       (8),
    .ADDR_WIDTH         (64),
    .DATA_WIDTH         (512),
    .ID_WIDTH           (8),
    .SEG_COUNT_WIDTH    (10),
    .PIPELINE           (0),
    .AR_MAX_OUTSTANDING (8)
) u_axi_read_engine (
    .clk                    (clk),
    .rst_n                  (rst_n),

    // Configuration
    .cfg_axi_rd_xfer_beats  (cfg_axi_rd_xfer_beats),

    // Scheduler interface
    .sched_rd_valid         (sched_rd_valid),
    .sched_rd_addr          (sched_rd_addr),
    .sched_rd_beats         (sched_rd_beats),

    // Completion interface
    .sched_rd_done_strobe   (sched_rd_done_strobe),
    .sched_rd_beats_done    (sched_rd_beats_done),

    // SRAM allocation interface
    .axi_rd_alloc_req       (axi_rd_alloc_req),
    .axi_rd_alloc_size      (axi_rd_alloc_size),
    .axi_rd_alloc_id        (axi_rd_alloc_id),
    .axi_rd_alloc_space_free(axi_rd_alloc_space_free),

    // SRAM write interface
    .axi_rd_sram_valid      (axi_rd_sram_valid),
    .axi_rd_sram_ready      (axi_rd_sram_ready),
    .axi_rd_sram_id         (axi_rd_sram_id),
    .axi_rd_sram_data       (axi_rd_sram_data),

    // AXI master
    .m_axi_arvalid          (m_axi_rd_arvalid),
    .m_axi_arready          (m_axi_rd_arready),
    .m_axi_arid             (m_axi_rd_arid),
    .m_axi_araddr           (m_axi_rd_araddr),
    .m_axi_arlen            (m_axi_rd_arlen),
    .m_axi_arsize           (m_axi_rd_arsize),
    .m_axi_arburst          (m_axi_rd_arburst),

    .m_axi_rvalid           (m_axi_rd_rvalid),
    .m_axi_rready           (m_axi_rd_rready),
    .m_axi_rid              (m_axi_rd_rid),
    .m_axi_rdata            (m_axi_rd_rdata),
    .m_axi_rresp            (m_axi_rd_rresp),
    .m_axi_rlast            (m_axi_rd_rlast),

    // Error and debug
    .sched_rd_error         (sched_rd_error),
    .dbg_rd_all_complete    (dbg_rd_all_complete),
    .dbg_arb_request        (dbg_arb_request)
);
```

---

## Related Documentation

- **Parent:** `01_stream_core.md` - Top-level integration
- **Scheduler Array:** `02_scheduler_group_array.md` - Provides sched_rd_* signals
- **Allocation Controller:** `07_stream_alloc_ctrl.md` - Space tracking for read engine
- **SRAM Controller:** `08_sram_controller.md` - Receives read data
- **Write Engine:** `12_axi_write_engine.md` - Complementary write datapath

---

**Last Updated:** 2025-11-30 (verified against RTL implementation)
