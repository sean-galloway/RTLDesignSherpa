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

# axi4ace_snoop_monitor_lite

ACE snoop-channel lite monitor for `cache-ip`. Tracks outstanding snoops in AC-issue order and emits error, timeout, and completion packets on the monbus.

## Overview

`axi4ace_snoop_monitor_lite` is the ACE snoop-channel counterpart to `axi_monitor_lite`. The standard `axi_monitor_lite` cannot monitor snoop channels because they have no transaction ID. This core keeps an in-order table of outstanding snoops, attributes each CR handshake and CDLAST beat to the oldest entry, and emits the same 128-bit `monitor_packet_t` records on the monbus.

The monitor is a TAP: it observes `ac_valid`/`ac_ready`, `cr_valid`/`cr_ready`, and `cd_valid`/`cd_ready`/`cd_last`, but never drives the observed channels.

## Why a Separate Monitor Core

ACE snoop channels differ from AXI4 channels in two ways that break per-ID tracking:

- **No ID field**: AC carries only address, snoop type, and protection; CR and CD carry no ID.
- **In-order attribution**: Responses and data must be returned in the order the ACs were issued.

Therefore the monitor cannot use a CAM or linked-list keyed by ID. It uses a circular FIFO of outstanding snoops in AC-issue order, with CR and CDLAST always attributed to the head entry.

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| UNIT_ID | logic [7:0] | 8'h01 | Unit ID in every emitted packet |
| AGENT_ID | logic [15:0] | 16'h000A | Agent ID in every emitted packet |
| MAX_SNOOPS | int | 8 | Outstanding-snoop table depth |
| OUT_DEPTH | int | 4 | monbus output queue depth, a power of two |
| ACLK_MHZ | int | 100 | Clock frequency in MHz for the frequency-invariant us tick |
| CFI_MIN_FREQ_MHZ | int | ACLK_MHZ | Frequency-invariant tick LUT lower bound |
| CFI_MAX_FREQ_MHZ | int | ACLK_MHZ | Frequency-invariant tick LUT upper bound |
| CFI_NUM_FREQ_ENTRIES | int | 16 | Number of frequency entries in the LUT |
| CFI_FREQ_STRATEGY | int | 0 | Frequency strategy selector |
| ADDR_WIDTH | int | 32 | Snoop address width |
| DATA_WIDTH | int | 32 | Snoop data width (used only for beat counting; data itself is not captured) |
| AW | int | ADDR_WIDTH | Short alias for address width |
| DW | int | DATA_WIDTH | Short alias for data width |
| N | int | MAX_SNOOPS | Short alias for table depth |
| SW | int | (N>1)?$clog2(N):1 | Table-index width |
| CW | int | $clog2(N+1) | Occupancy-counter width |
| SELW | int | (CFI_NUM_FREQ_ENTRIES>1)?$clog2(CFI_NUM_FREQ_ENTRIES):1 | `cfg_freq_sel` width |
| TS_WIDTH | int | 16 | Timestamp / latency width |
| AGE_WIDTH | int | 16 | Internal us-counter and age width |

## Ports

| Port | Direction | Type | Description |
|------|-----------|------|-------------|
| aclk | input | logic | AXI clock |
| aresetn | input | logic | Active-low reset |
| clear | input | logic | Synchronous clear; also driven by `~cfg_monitor_enable` in wrappers |
| i_mon_time | input | `monitor_common_pkg::monbus_timestamp_t` | Free-running broadcast timestamp |
| cfg_monitor_enable | input | logic | 0 = monitor inert, table held clear |
| cfg_error_enable | input | logic | Enable error packet emission |
| cfg_compl_enable | input | logic | Enable completion packet emission |
| cfg_timeout_enable | input | logic | Enable timeout detection and packet emission |
| cfg_timeout_cycles | input | logic [15:0] | Timeout in microseconds; 0 = never, 0xFFFF = never |
| cfg_freq_sel | input | logic [SELW-1:0] | Frequency-invariant tick LUT index |
| monbus_valid | output | logic | monbus packet valid |
| monbus_ready | input | logic | monbus consumer ready |
| monbus_packet | output | `monitor_common_pkg::monitor_packet_t` | 128-bit monitor packet |
| monbus_timestamp | output | `monitor_common_pkg::monbus_timestamp_t` | Side-band timestamp |
| active_transactions | output | logic [7:0] | Entries currently in the snoop table |
| error_count | output | logic [15:0] | Error + timeout packets emitted |
| transaction_count | output | logic [31:0] | Completion packets emitted |
| dropped_count | output | logic [15:0] | Events lost to monbus backpressure since last report |
| ac_addr | input | logic [AW-1:0] | AC address observation tap |
| ac_snoop | input | logic [3:0] | AC snoop type observation tap |
| ac_valid | input | logic | AC valid observation tap |
| ac_ready | input | logic | AC ready observation tap |
| cr_resp | input | logic [4:0] | CR response observation tap |
| cr_valid | input | logic | CR valid observation tap |
| cr_ready | input | logic | CR ready observation tap |
| cd_last | input | logic | CD last-beat observation tap |
| cd_valid | input | logic | CD valid observation tap |
| cd_ready | input | logic | CD ready observation tap |

## Packet Encoding

All packets carry `protocol = PROTOCOL_AXI`.

### Completion Packet (`PktTypeCompletion`)

| Field | Value | Notes |
|-------|-------|-------|
| event_code | `{CRRESP[3:0], ACSNOOP[3:0]}` | Lower 4 bits = snoop type that started the transaction; upper 4 bits = response code |
| channel_id | CDLAST beat count for this snoop | Saturated to 9 bits; the snoop type is already in `event_code` |
| event_data | `{latency[15:0], ACADDR[AW-1:0]}` | Latency (cycles) occupies `event_data[63:48]`; address occupies the lower bits. For `AW > 48` the top address bits share the latency field, matching the trade-off in `axi_monitor_lite`. |
| latency | `i_mon_time - AC handshake i_mon_time` | Cycles |

### Error Packet (`PktTypeError`)

| Condition | `event_code` | Notes |
|-----------|--------------|-------|
| CRRESP[1] set (Error) | `AXI_ERR_PROTOCOL` | Only when `cfg_error_enable` is high |
| CR handshake with no AC pending | `AXI_ERR_RESP_ORPHAN` | Response arrived while table empty |
| CDLAST handshake with no AC pending | `AXI_ERR_DATA_ORPHAN` | Data arrived while table empty |

### Timeout Packet (`PktTypeTimeout`)

| Condition | `event_code` | Notes |
|-----------|--------------|-------|
| Head entry older than `cfg_timeout_cycles` us | `AXI_TIMEOUT_RESP` | Only the head can age out; a CR or CD handshake on the head resets its progress stamp |

### Event Precedence

When multiple events are ready in the same cycle, only one packet is emitted. Priority is:

```text
ERROR > TIMEOUT > COMPLETION
```

When `CRRESP[1]` is set and `cfg_error_enable` is high, an ERROR packet is emitted and the COMPLETION packet for that snoop is suppressed.

## Drop-and-Count Discipline

The monitor never stalls the observed channels. Events that cannot be queued in the `OUT_DEPTH` output queue are dropped and counted. The count is emitted as an `AXI_ERR_EVENT_DROPPED` packet when the queue has room and no other event wants the bus.

A snoop that arrives when the table is full is counted as `refused` and left untracked. Any later CR/CD for that snoop reports as an orphan error. The monitor core itself does not expose `refused_count`; the wrappers that instantiate it may choose to expose or aggregate it.

## Outstanding-Snoop Table

The table is a circular FIFO:

- `r_rd_ptr` points to the oldest outstanding snoop
- `r_wr_ptr` points to the next free tail
- CR and CDLAST are attributed to the head entry
- Only the head can timeout
- Multiple outstanding snoops are allowed

This matches ACE's per-channel ordering rule: CR responses and CD data must be returned in the same order as the AC addresses.

## Wrappers that Instantiate This Core

The snoop-side `_monlite` wrappers instantiate `axi4ace_snoop_monitor_lite`. See [axi_monitor_lite_wrappers.md](axi_monitor_lite_wrappers.md) for wrapper details.

| Wrapper | Direction | Core wrapped | Monitor taps |
|---------|-----------|--------------|--------------|
| `axi4ace_snoop_slave_monlite` | Cache side | `axi4ace_snoop_slave` | `m_axi_ac*` / `m_axi_cr*` / `m_axi_cd*` |
| `axi4ace_snoop_master_monlite` | CCU side | `axi4ace_snoop_master` | `m_axi_ac*` / `m_axi_cr*` / `m_axi_cd*` |

## Related Modules

- [axi_monitor_lite](axi_monitor_lite.md) — AXI/AXIL transaction lite monitor (per-ID tracking)
- [axi_monitor_lite_wrappers](axi_monitor_lite_wrappers.md) — the two snoop-side wrappers that use this core
- [axi4ace_snoop_slave](../ace/axi4ace_snoop_slave.md) — cache-side snoop responder transport
- [axi4ace_snoop_master](../ace/axi4ace_snoop_master.md) — CCU-side snoop initiator transport

---

## Navigation

- **[← Back to Monitor Index](../_book_monitor_index.md)**
- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
