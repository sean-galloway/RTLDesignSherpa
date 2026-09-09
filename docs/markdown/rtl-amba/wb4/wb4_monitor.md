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

# wb4_monitor

## Overview

`wb4_monitor` watches the `cmd_*`/`rsp_*` queues of a `wb4_master` or
`wb4_slave` and reports what happens on the Wishbone side as monitor bus
packets: a completion or an error per transfer, a timeout when a request or
a termination is late, a latency figure when a transfer crosses a threshold,
optional queue-activity debug events, and address-range violations through
the shared `apb_monitor_addr_check`. It is the Wishbone member of the
monitor family and has the same configuration, monitor bus and status ports
as `apb4_monitor`; every packet is tagged `PROTOCOL_WB` (`4'h5`) and its
event codes come from `monitor_wb4_pkg`.

The queues are the timing-convenient proxy for the bus, the same place
`apb4_monitor` attaches: a command handshake is a request the master will
put on the bus, a response handshake is the termination the slave returned.
One difference from APB matters for the design: Wishbone B4 pipelined mode
keeps several transfers open, and terminates them **in issue order**. The
monitor therefore tracks transfers in an in-order queue, not a slot table.
A slot table that pairs a response with "the first active slot" mis-pairs as
soon as a freed slot is reused while an older one is still open, which
pipelined traffic does constantly. The in-order queue pairs the response
with the oldest open request by construction.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| USE_MONITOR | bit | 1 | 0 removes the body and ties the outputs to idle |
| N_ADDR_RANGES | int | 0 | Address-range checker ranges; 0 leaves the checker out |
| ADDR_WIDTH | int | 32 | Wishbone address width |
| DATA_WIDTH | int | 32 | Wishbone data width |
| UNIT_ID | logic [7:0] | 8'h01 | Unit id stamped into every packet |
| AGENT_ID | logic [15:0] | 16'h000B | Agent id stamped into every packet |
| MAX_TRANSACTIONS | int | 8 | Depth of the in-order tracking queue; transfers open at once beyond it are reported, not tracked |
| MONITOR_FIFO_DEPTH | int | 8 | Event FIFO depth between event selection and the monitor bus |

`MAX_TRANSACTIONS` should match the `RSP_DEPTH` of the `wb4_master` (or the
`MAX_OUTSTANDING` of the `wb4_slave`) it watches; those bound how many
transfers can be open, so a queue of the same depth never overflows.

## Ports

```systemverilog
module wb4_monitor
    import monitor_common_pkg::*;   // PROTOCOL_WB, PktType*, packet builder
    import monitor_wb4_pkg::*;      // WB_ERR_*, WB_TIMEOUT_*, WB_COMPL_*, WB_PERF_*, WB_DEBUG_*
    import wb4_pkg::*;              // WB4_RSP_* status encoding
#(
    parameter bit USE_MONITOR         = 1'b1,
    parameter int N_ADDR_RANGES       = 0,
    parameter int ADDR_WIDTH          = 32,
    parameter int DATA_WIDTH          = 32,
    parameter logic [7:0]  UNIT_ID    = 8'h01,
    parameter logic [15:0] AGENT_ID   = 16'h000B,
    parameter int MAX_TRANSACTIONS    = 8,
    parameter int MONITOR_FIFO_DEPTH  = 8
)
(
    input  logic                     aclk,
    input  logic                     aresetn,

    // Command queue being watched
    input  logic                     cmd_valid,
    input  logic                     cmd_ready,
    input  logic                     cmd_we,
    input  logic [AW-1:0]            cmd_adr,
    input  logic [DW-1:0]            cmd_dat,
    input  logic [SW-1:0]            cmd_sel,

    // Response queue being watched
    input  logic                     rsp_valid,
    input  logic                     rsp_ready,
    input  logic [1:0]               rsp_status,     // WB4_RSP_ACK / ERR / RTY
    input  logic [DW-1:0]            rsp_dat,

    // Configuration (same set as apb4_monitor)
    input  logic                     cfg_error_enable,
    input  logic                     cfg_timeout_enable,
    input  logic                     cfg_protocol_enable,
    input  logic                     cfg_slverr_enable,
    input  logic                     cfg_perf_enable,
    input  logic                     cfg_latency_enable,
    input  logic                     cfg_throughput_enable,
    input  logic                     cfg_debug_enable,
    input  logic                     cfg_trans_debug_enable,
    input  logic [3:0]               cfg_debug_level,
    input  logic [15:0]              cfg_cmd_timeout_cnt,
    input  logic [15:0]              cfg_rsp_timeout_cnt,
    input  logic [31:0]              cfg_latency_threshold,
    input  logic [15:0]              cfg_throughput_threshold,

    // Address-range checker configuration (N_ADDR_RANGES > 0)
    input  logic                     cfg_addr_check_enable,
    input  logic [N-1:0]             cfg_addr_range_enable,
    input  logic [N-1:0][AW-1:0]     cfg_addr_range_low,
    input  logic [N-1:0][AW-1:0]     cfg_addr_range_high,

    input  monbus_timestamp_t        i_mon_time,

    // Monitor bus
    output logic                     monbus_valid,
    input  logic                     monbus_ready,
    output monitor_packet_t          monbus_packet,
    output monbus_timestamp_t        monbus_timestamp,

    // Status
    output logic [7:0]               active_count,
    output logic [15:0]              error_count,
    output logic [31:0]              transaction_count
);
```

### Command and Response Queues

The monitor is a pure observer: it samples `cmd_valid && cmd_ready` and
`rsp_valid && rsp_ready` and never drives either queue. `cmd_dat` is
accepted for port uniformity and not used; `rsp_dat` is reported only in
the orphan-response packet.

### Configuration

| Signal | Effect |
|---|---|
| `cfg_error_enable` | Master enable for error packets |
| `cfg_slverr_enable` | Report an `ERR` termination as `WB_ERR_ERR` (counted in `error_count` either way) |
| `cfg_protocol_enable` | Report a response with nothing outstanding as `WB_ERR_ORPHAN_RSP` |
| `cfg_timeout_enable` | Enable both timeouts; a count of 0 disables that timeout |
| `cfg_cmd_timeout_cnt` | Clocks a request may sit on `cmd_valid` without `cmd_ready` before `WB_TIMEOUT_CMD` |
| `cfg_rsp_timeout_cnt` | Clocks the oldest open transfer may wait for its termination before `WB_TIMEOUT_RSP` |
| `cfg_perf_enable`, `cfg_latency_enable` | Emit a latency packet when a transfer's latency exceeds `cfg_latency_threshold` |
| `cfg_debug_enable`, `cfg_trans_debug_enable` | Emit `WB_DEBUG_QUEUE_ACTIVE` / `WB_DEBUG_QUEUE_IDLE` on the tracking queue's edges |
| `cfg_throughput_*`, `cfg_debug_level` | Accepted for family uniformity; no packet today |

### Status

`active_count` is the number of tracked transfers open right now,
`transaction_count` the number terminated since reset, and `error_count`
the number of `ERR` terminations (when `cfg_slverr_enable`), orphan
responses and tracking overflows.

## Functional Description

### Transaction Tracking

A command handshake pushes `{we, adr, sel[3:0], timestamp}` at the tail of
the queue; a response handshake pops the head. The head is the transfer the
response belongs to, because B4 terminates in issue order. Two edge cases
are reported rather than guessed at:

- **Orphan response.** A response handshake with an empty queue. With
  `cfg_protocol_enable` it is a `WB_ERR_ORPHAN_RSP` packet carrying
  `rsp_dat` and the status; `transaction_count` does not move.
- **Tracking lost.** A command handshake with the queue full. The transfer
  is not tracked (its later response will show up as an orphan) and a
  `WB_ERR_TRACK_LOST` packet carries its address. Size `MAX_TRANSACTIONS`
  to the master's `RSP_DEPTH` and this never happens.

### Event Detection

| Event | Packet type | Event code | event_data[31:0] | aux (event_data[39:32]) |
|---|---|---|---|---|
| Termination `ACK` | Completion | `WB_COMPL_READ` / `WB_COMPL_WRITE` | address | `{3'b0, sel[3:0], we}` |
| Termination `RTY` | Completion | `WB_COMPL_RTY` | address | `{3'b0, sel[3:0], we}` |
| Termination `ERR` | Error | `WB_ERR_ERR` | address | `{3'b0, sel[3:0], we}` |
| Response, nothing open | Error | `WB_ERR_ORPHAN_RSP` | `rsp_dat` | `{6'b0, status}` |
| Command, queue full | Error | `WB_ERR_TRACK_LOST` | address | `{3'b0, sel[3:0], we}` |
| `cmd_valid` stalled | Timeout | `WB_TIMEOUT_CMD` | address on `cmd_adr` | stall count (low 8 bits) |
| Head transfer late | Timeout | `WB_TIMEOUT_RSP` | head address | age (low 8 bits) |
| Latency over threshold | Perf | `WB_PERF_READ_LATENCY` / `WB_PERF_WRITE_LATENCY` | latency in clocks | `{3'b0, sel[3:0], we}` |
| Queue non-empty / empty | Debug | `WB_DEBUG_QUEUE_ACTIVE` / `WB_DEBUG_QUEUE_IDLE` | occupancy | 0 |
| Address out of range | Error | `WB_ERR_ADDR_RANGE` | see `apb_monitor_addr_check` | see `apb_monitor_addr_check` |

`RTY` is a completion, not an error: the FUB decides whether to retry, and
the monitor reports what the slave said. Each timeout fires **once**: the
command timeout once per stall (it re-arms when the request is taken or
withdrawn), the response timeout once per queue entry (a flag in the entry).
When the head pops and the next entry is already older than the limit, that
entry is reported on the following clock.

### Monitor Packet Format

Standard 128-bit packet from `create_monitor_packet` with a 64-bit
side-band timestamp taken from `i_mon_time` at emission:

- `packet_type` per the table above; `protocol` = `PROTOCOL_WB` (`4'h5`)
- `event_code` from `monitor_wb4_pkg`; `channel_id` = 0 (Wishbone has no IDs)
- `unit_id` = `UNIT_ID`, `agent_id` = `AGENT_ID`
- `event_data[63:40]` = 0, `[39:32]` = aux, `[31:0]` = value per the table

### Event Priority and Loss

One event is written to the FIFO per clock, in the order error, timeout,
perf, debug, completion; a lower-priority event that lands in the same
clock as a higher one is dropped, and so is any event that arrives while
the FIFO is full. The tracking queue does not wait for the packet, so
`active_count`, `transaction_count` and `error_count` stay exact. This is
the family's lossy-but-honest contract; size `MONITOR_FIFO_DEPTH` and the
monitor bus consumer for the burstiest traffic the design can produce.

The event FIFO is a `gaxi_fifo_sync` in mux-read mode (`REGISTERED=0`):
`rd_data` is valid in the clock of the read handshake, which is when the
packet is built. The registered-read mode presents `rd_data` one clock
after the handshake (the framework's `fifo_flop` BFM contract) and, read
combinationally, re-presents the popped entry for a clock on back-to-back
reads, so a burst of events would duplicate one packet and lose the next.
This module's first test caught exactly that; see TASK-086 for the siblings.

## Timing Characteristics

- Push and pop are registered from the queue handshakes; `active_count`
  updates on the clock after a handshake.
- A completion packet leaves the event FIFO one clock after the response
  handshake and the skid buffer one clock later, so `monbus_valid` for a
  termination rises two clocks after `rsp_valid && rsp_ready` when the bus
  is idle.
- `monbus_valid` is held until `monbus_ready` (skid buffer).

## Usage Example

```systemverilog
wb4_monitor #(
    .ADDR_WIDTH       (32),
    .DATA_WIDTH       (32),
    .UNIT_ID          (8'h02),
    .AGENT_ID         (16'h0020),
    .MAX_TRANSACTIONS (4),          // = wb4_master RSP_DEPTH
    .N_ADDR_RANGES    (2)
) u_wb_mon (
    .aclk (clk), .aresetn (rst_n),
    .cmd_valid (cmd_valid), .cmd_ready (cmd_ready), .cmd_we (cmd_we),
    .cmd_adr (cmd_adr), .cmd_dat (cmd_dat), .cmd_sel (cmd_sel),
    .rsp_valid (rsp_valid), .rsp_ready (rsp_ready),
    .rsp_status (rsp_status), .rsp_dat (rsp_dat),
    .cfg_error_enable (1'b1), .cfg_timeout_enable (1'b1),
    .cfg_protocol_enable (1'b1), .cfg_slverr_enable (1'b1),
    .cfg_perf_enable (1'b0), .cfg_latency_enable (1'b0),
    .cfg_throughput_enable (1'b0), .cfg_debug_enable (1'b0),
    .cfg_trans_debug_enable (1'b0), .cfg_debug_level (4'h0),
    .cfg_cmd_timeout_cnt (16'd256), .cfg_rsp_timeout_cnt (16'd1024),
    .cfg_latency_threshold (32'd0), .cfg_throughput_threshold (16'd0),
    .cfg_addr_check_enable (1'b1), .cfg_addr_range_enable (2'b11),
    .cfg_addr_range_low ('{32'h0000_0000, 32'h4000_0000}),
    .cfg_addr_range_high ('{32'h0FFF_FFFF, 32'h4FFF_FFFF}),
    .i_mon_time (mon_time),
    .monbus_valid (monbus_valid), .monbus_ready (monbus_ready),
    .monbus_packet (monbus_packet), .monbus_timestamp (monbus_timestamp),
    .active_count (), .error_count (), .transaction_count ()
);
```

## Notes

- Under `ifdef FORMAL` the block asserts the queue occupancy bound, that a
  pop only happens with something open, and that an orphan is only flagged
  when nothing is. `formal/amba/wb4_monitor/` adds the port-level
  properties (reset, protocol tag, valid-held, occupancy tracks the
  handshakes, `transaction_count` moves only on a pop) and covers every
  packet class.
- `USE_MONITOR=0` leaves the ports in place and ties `monbus_valid` and the
  counters to zero, so a build can drop the monitor without touching the
  wrapper.
- `monitor_wb4_pkg` is imported by this module only; it is deliberately not
  re-exported by `monitor_pkg`, so no existing consumer's filelist changes.
  `PROTOCOL_WB` itself lives in `monitor_common_pkg` (an additive enum entry).

## Related

- [wb4_master](wb4_master.md), [wb4_slave](wb4_slave.md) - what it watches
- [apb4_monitor](../apb4/apb4_monitor.md) - the family template
- [apb_monitor_addr_check](../monitor/apb_monitor_addr_check.md) - the shared range checker, tagged `PROTOCOL_WB` here through its `PROTOCOL` parameter
- [monitor_package_spec](../includes/monitor_package_spec.md) - packet format and protocol ids

## Test

`val/amba/test_wb4_monitor.py` drives both queues with GAXI BFMs (a
producer/consumer pair on each side, an age-based responder) and decodes
the packets through the shared `MonbusSlave`/`TBClasses.monbus.parse`
path. Phases: ACK/ERR/RTY mix in command order, several transfers open
(in-order pairing), latency threshold, both timeouts once each, orphan,
tracking overflow, debug edges, and address range on the `N_ADDR_RANGES=2`
build. Four RTL mutations (timeout re-fire, swapped read/write codes,
pairing off by one, orphan not reported) all fail the test.
