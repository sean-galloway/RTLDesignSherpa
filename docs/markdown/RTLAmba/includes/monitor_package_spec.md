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

# Monitor Package Specification

This is the canonical reference for the monitor-bus packet format and the
universal types shared by every protocol monitor in the AMBA subsystem.
For per-protocol event-code enums see the three sibling docs:

- [`monitor_amba4_pkg.md`](./monitor_amba4_pkg.md) — AXI4 / APB4 / AXIS4 event codes
- [`monitor_amba5_pkg.md`](./monitor_amba5_pkg.md) — AXI5 / APB5 / AXIS5 extended codes
- [`monitor_arbiter_pkg.md`](./monitor_arbiter_pkg.md) — ARB and CORE event codes

---

## Package Organization

The RTL splits monitor type definitions across four SystemVerilog packages:

| Package | File | Purpose |
|---------|------|---------|
| `monitor_common_pkg`  | `rtl/amba/includes/monitor_common_pkg.sv`  | Universal types: packet structure, timestamp, protocol enum, packet-type enum, helper functions. **This doc.** |
| `monitor_amba4_pkg`   | `rtl/amba/includes/monitor_amba4_pkg.sv`   | AXI4 / APB4 / AXIS4 event-code enums (error / timeout / completion / threshold / perf / addr-match / debug). |
| `monitor_amba5_pkg`   | `rtl/amba/includes/monitor_amba5_pkg.sv`   | AXI5 / APB5 / AXIS5 extended event-code enums (atomic, trace, wakeup, parity, user). |
| `monitor_arbiter_pkg` | `rtl/amba/includes/monitor_arbiter_pkg.sv` | ARB and CORE event codes for arbiter monitors and custom subsystems. |

A wrapper `monitor_pkg` re-exports all four for back-compatibility — code that
imports `monitor_pkg::*;` continues to compile unchanged.

---

## The Monbus Record

A monbus emission is two paired wires carried atomically through every level
of the transport: a **128-bit packet** (`monbus_packet`) plus a **64-bit
side-band timestamp** (`monbus_timestamp`). 192 bits total.

| Wire | Bits | Width | Field | Owner | Notes |
|------|------|------:|-------|-------|-------|
| `monbus_timestamp` | [63:0]    | 64 | timestamp     | system        | Free-running counter from `monbus_axil_group`, sampled at emission. Consumers treat it as an opaque ordering key. |
| `monbus_packet`    | [127:124] |  4 | packet_type   | enum (fixed)  | See [Packet Type Enum](#packet-type-enum). |
| `monbus_packet`    | [123:109] | 15 | reserved      | (slack)       | Currently emitted as zero. |
| `monbus_packet`    | [108:105] |  4 | protocol      | enum (fixed)  | See [Protocol Enum](#protocol-enum). |
| `monbus_packet`    | [104:97]  |  8 | event_code    | enum (fixed)  | Protocol-specific; see sibling docs. |
| `monbus_packet`    | [96:88]   |  9 | channel_id    | **designer**  | AXI ID or channel index. |
| `monbus_packet`    | [87:72]   | 16 | agent_id      | **designer**  | Designer-allocated agent ID. |
| `monbus_packet`    | [71:64]   |  8 | unit_id       | **designer**  | Designer-allocated unit ID. |
| `monbus_packet`    | [63:0]    | 64 | event_data    | payload       | Layout depends on (packet_type, event_code) — see [event_data Payload Conventions](#event_data-payload-conventions). |

### SystemVerilog Type Aliases

```systemverilog
localparam int MONBUS_PKT_WIDTH = 128;
localparam int MONBUS_TS_WIDTH  =  64;

typedef logic [MONBUS_PKT_WIDTH-1:0] monitor_packet_t;
typedef logic [MONBUS_TS_WIDTH-1:0]  monbus_timestamp_t;
```

The widths are localparams in `monitor_common_pkg`, **not** per-module
parameters — there is exactly one packet format and one timestamp format
across the codebase. Any consumer that declares a bus or FIFO holding a
packet must reference these constants, not hard-code `128` / `64`.

---

## Protocol Enum

The 4-bit `protocol` field identifies which protocol family produced the
event. The enum is defined in `monitor_common_pkg`:

| Value | Name             | Description |
|------:|------------------|-------------|
| 4'h0  | `PROTOCOL_AXI`   | AXI / AXI-Lite / AXI5 |
| 4'h1  | `PROTOCOL_AXIS`  | AXI4-Stream |
| 4'h2  | `PROTOCOL_APB`   | Advanced Peripheral Bus (APB4 / APB5) |
| 4'h3  | `PROTOCOL_ARB`   | Arbiter-specific events |
| 4'h4  | `PROTOCOL_CORE`  | Core / custom subsystem events |
| 4'h5–4'hF | (reserved)   | Forward-compat slack — 16 protocols max. |

```systemverilog
typedef enum logic [3:0] {
    PROTOCOL_AXI   = 4'h0,
    PROTOCOL_AXIS  = 4'h1,
    PROTOCOL_APB   = 4'h2,
    PROTOCOL_ARB   = 4'h3,
    PROTOCOL_CORE  = 4'h4
} protocol_type_t;
```

---

## Packet Type Enum

The 4-bit `packet_type` field classifies the event independent of protocol.
The 16 codes are defined as localparams in `monitor_common_pkg`:

| Value | Name               | Description |
|------:|--------------------|-------------|
| 4'h0  | `PktTypeError`     | Protocol violation, SLVERR/DECERR, orphan, range violation |
| 4'h1  | `PktTypeCompletion`| Transaction completed successfully |
| 4'h2  | `PktTypeThreshold` | Threshold crossed (latency, queue depth, etc.) |
| 4'h3  | `PktTypeTimeout`   | Timeout detected on command / data / response phase |
| 4'h4  | `PktTypePerf`      | Performance metric event |
| 4'h5  | `PktTypeCredit`    | Credit status (AXIS) |
| 4'h6  | `PktTypeChannel`   | Channel status (AXIS) |
| 4'h7  | `PktTypeStream`    | Stream event (AXIS — start/end/abort) |
| 4'h8  | `PktTypeAddrMatch` | Address-match watchpoint (AXI) |
| 4'h9  | `PktTypeAPB`       | APB-specific event |
| 4'hA–4'hE | (reserved)     | Forward-compat slack |
| 4'hF  | `PktTypeDebug`     | Debug / trace event |

```systemverilog
localparam logic [3:0] PktTypeError      = 4'h0;
localparam logic [3:0] PktTypeCompletion = 4'h1;
localparam logic [3:0] PktTypeThreshold  = 4'h2;
localparam logic [3:0] PktTypeTimeout    = 4'h3;
localparam logic [3:0] PktTypePerf       = 4'h4;
localparam logic [3:0] PktTypeCredit     = 4'h5;
localparam logic [3:0] PktTypeChannel    = 4'h6;
localparam logic [3:0] PktTypeStream     = 4'h7;
localparam logic [3:0] PktTypeAddrMatch  = 4'h8;
localparam logic [3:0] PktTypeAPB        = 4'h9;
localparam logic [3:0] PktTypeDebug      = 4'hF;
```

---

## event_data Payload Conventions

The 64-bit `event_data` field is interpreted in the context of
`(packet_type, event_code)`. There is no universal layout — each producer
defines its own packing. The table below lists the most common shapes:

| Producer | packet_type | event_code | event_data layout |
|----------|-------------|------------|-------------------|
| `axi_monitor_addr_check`  | Error  | `AXI_ERR_ADDR_RANGE` (8'h0D) | `[63:60]` = range_index (4b), `[59:0]` = full matched address |
| `apb_monitor_addr_check`  | Error  | `APB_ERR_ADDR_RANGE` (8'h0D) | `[63:60]` = range_index (4b), `[59]` = is_read, `[58:0]` = address |
| `axi_monitor_reporter`    | Error / Timeout / Completion | various | Full 64-bit address, or zero-extended ID / latency / counter |
| `axi_monitor_reporter`    | Perf   | `AXI_PERF_*`        | Zero-extended counter value (completed/error counts, latencies) |
| `axi_monitor_reporter`    | Threshold | `AXI_THRESH_ACTIVE_COUNT` | Zero-extended active-transaction count |
| `arbiter_monbus_common`   | Error / Perf | `ARB_*`        | Arbiter-specific payload (winning client, weight, etc.) |

Notable design rule: **direction is not embedded in event_data for AXI
addr_check.** Each AXI monitor instance watches a single direction (AR or AW)
set at build time via the `IS_READ` parameter; consumers recover direction
from the emitting monitor's `(unit_id, agent_id)` tuple. APB addr_check is
the exception — one APB monitor sees both reads and writes on the same
channel, so it carries an explicit `is_read` flag.

---

## Helper Functions

Field accessors and a packet builder are declared in `monitor_common_pkg`:

```systemverilog
function automatic logic [3:0]      get_packet_type   (monitor_packet_t pkt); return pkt[127:124]; endfunction
function automatic logic [14:0]     get_reserved      (monitor_packet_t pkt); return pkt[123:109]; endfunction
function automatic protocol_type_t  get_protocol_type (monitor_packet_t pkt); return protocol_type_t'(pkt[108:105]); endfunction
function automatic logic [7:0]      get_event_code    (monitor_packet_t pkt); return pkt[104:97];  endfunction
function automatic logic [8:0]      get_channel_id    (monitor_packet_t pkt); return pkt[96:88];   endfunction
function automatic logic [15:0]     get_agent_id      (monitor_packet_t pkt); return pkt[87:72];   endfunction
function automatic logic [7:0]      get_unit_id       (monitor_packet_t pkt); return pkt[71:64];   endfunction
function automatic logic [63:0]     get_event_data    (monitor_packet_t pkt); return pkt[63:0];    endfunction

function automatic monitor_packet_t create_monitor_packet(
    logic [3:0]     packet_type,
    protocol_type_t protocol,
    logic [7:0]     event_code,
    logic [8:0]     channel_id,
    logic [7:0]     unit_id,
    logic [15:0]    agent_id,
    logic [63:0]    event_data
);
    return {packet_type, 15'h0, protocol, event_code,
            channel_id, agent_id, unit_id, event_data};
endfunction
```

`create_monitor_packet` zeroes the reserved field; do not rely on its bits.

### Construction Example

```systemverilog
// AXI master-side wrapper emits a range-violation error packet
monitor_packet_t pkt = create_monitor_packet(
    .packet_type ( PktTypeError                          ),
    .protocol    ( PROTOCOL_AXI                          ),
    .event_code  ( AXI_ERR_ADDR_RANGE                    ),  // 8'h0D
    .channel_id  ( 9'(cmd_id)                            ),
    .unit_id     ( UNIT_ID                               ),  // build-time
    .agent_id    ( AGENT_ID                              ),  // build-time
    .event_data  ( {range_index[3:0], 60'(cmd_addr)}     )
);
```

The wrapper drives `pkt` on `monbus_packet` and the sampled `i_mon_time` on
`monbus_timestamp` in the same cycle.

---

## Side-Band Timestamp

The timestamp lives outside the packet so the packet layout is fixed at 128
bits and `create_monitor_packet` doesn't need a timestamp argument.

```systemverilog
typedef logic [MONBUS_TS_WIDTH-1:0] monbus_timestamp_t;  // 64 bits
```

| Stage | Wire | Notes |
|-------|------|-------|
| Source | `i_mon_time` | A free-running counter generated in `monbus_axil_group` and broadcast to every wrapper via the shared `mon_time_w` net. |
| Sampling | `addr_pkt_timestamp` / `monbus_timestamp` | Each producer (addr_check, reporter, debug) samples `i_mon_time` on the cycle its packet asserts valid. |
| Transport | `monbus_arbiter` | The arbiter carries `(packet, timestamp)` atomically through a 192-bit skid so consumers never see a mismatched pair. |
| Drain | `monbus_axil_group` | Emits a 3-beat record on `m_mon_axil` (`[pkt[63:0], pkt[127:64], ts[63:0]]`) for bulk capture, or single-record reads via `s_mon_axil` for IRQ-driven consumption. |

Consumers (host scripts, parsers, the `bin/TBClasses/monbus` decoder) treat
the timestamp as an opaque ordering key — its semantics (cycle counter,
microsecond, PTP time) are deployment-specific. See
[`monitor_system_whitepaper.md`](../monitor_system_whitepaper.md) §3 for
timestamp-policy tradeoffs.

---

## Per-Protocol Event Code Packages

Each event-code enum is 8 bits wide and lives in the protocol-specific
sibling package. The pattern is:

```
event_code  =  enum value from
                  monitor_{amba4,amba5,arbiter}_pkg::{protocol}_{category}_code_t
```

Categories per protocol (each ~16-entry enum):

| Package | Protocol | Categories |
|---------|----------|------------|
| `monitor_amba4_pkg` | AXI4  | error, timeout, completion, threshold, performance, addr_match, debug |
| `monitor_amba4_pkg` | APB4  | error, timeout, completion, threshold, performance, debug |
| `monitor_amba4_pkg` | AXIS4 | error, timeout, completion, credit, channel, stream |
| `monitor_amba5_pkg` | AXI5  | atomic, trace |
| `monitor_amba5_pkg` | APB5  | wakeup, parity, user |
| `monitor_amba5_pkg` | AXIS5 | wakeup, parity |
| `monitor_arbiter_pkg` | ARB | error, timeout, completion, threshold, performance, debug |
| `monitor_arbiter_pkg` | CORE | error, timeout, completion, threshold, performance, debug |

Full enum-value tables are in the sibling docs.

---

## Backward Compatibility

The aggregating wrapper `monitor_pkg` re-exports every type from the four
split packages, so existing code that does:

```systemverilog
import monitor_pkg::*;
```

continues to compile. New code should import the specific package it needs:

```systemverilog
// Universal types
import monitor_common_pkg::*;

// Plus the protocol you actually use:
import monitor_amba4_pkg::*;
```

This keeps namespace pollution down and makes the dependency graph
explicit at the file level.

---

## Related Documentation

- **[`monitor_system_whitepaper.md`](../monitor_system_whitepaper.md)** — Design-surface view: identity allocation, timestamp policy, drain paths, aggregation topology.
- **[`shared/axi_monitor_base.md`](../shared/axi_monitor_base.md)** — Core monitor that emits packets.
- **[`shared/axi_monitor_reporter.md`](../shared/axi_monitor_reporter.md)** — Packet formatting logic (where `create_monitor_packet` is invoked).
- **[`shared/axi_monitor_addr_check.md`](../shared/axi_monitor_addr_check.md)** — Address-range checker, canonical example of structured `event_data`.
- **[`shared/monbus_arbiter.md`](../shared/monbus_arbiter.md)** — 192-bit atomic packet+timestamp arbitration.

---

## Navigation

- **[← Back to Includes Index](./README.md)**
- **[← Back to RTLAmba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
