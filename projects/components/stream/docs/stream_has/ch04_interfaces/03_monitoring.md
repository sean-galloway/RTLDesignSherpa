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

# Monitoring Interface

## Overview

STREAM provides a 64-bit Monitor Bus (MonBus) interface for debug and performance monitoring. This interface streams event packets capturing key operational events.

---

## Signal Summary

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `monbus_pkt_valid` | Output | 1 | Packet valid |
| `monbus_pkt_ready` | Input | 1 | Downstream ready |
| `monbus_pkt_data` | Output | 64 | Packet data |

---

## Packet Format

Each 64-bit MonBus packet follows this format:

| Bits | Field | Description |
|------|-------|-------------|
| [63:56] | `SUBSYSTEM_ID` | STREAM subsystem identifier |
| [55:48] | `EVENT_TYPE` | Event category |
| [47:40] | `EVENT_CODE` | Specific event within category |
| [39:32] | `CHANNEL_ID` | Associated channel (0-7) |
| [31:0] | `PAYLOAD` | Event-specific data |

---

## Event Types

### Transfer Events (EVENT_TYPE = 0x01)

| EVENT_CODE | Event | Payload |
|------------|-------|---------|
| 0x01 | `KICKOFF` | Descriptor address [31:0] |
| 0x02 | `DESC_FETCH` | Descriptor address [31:0] |
| 0x03 | `DESC_VALID` | Descriptor fields summary |
| 0x04 | `READ_START` | Source address [31:0] |
| 0x05 | `READ_DONE` | Beat count |
| 0x06 | `WRITE_START` | Destination address [31:0] |
| 0x07 | `WRITE_DONE` | Beat count |
| 0x08 | `CHAIN_NEXT` | Next descriptor address |
| 0x09 | `COMPLETE` | Total descriptors processed |

### Error Events (EVENT_TYPE = 0x02)

| EVENT_CODE | Event | Payload |
|------------|-------|---------|
| 0x01 | `AXI_READ_ERR` | AXI response code |
| 0x02 | `AXI_WRITE_ERR` | AXI response code |
| 0x03 | `DESC_INVALID` | Validation failure code |
| 0x04 | `ADDR_RANGE` | Offending address [31:0] |
| 0x05 | `TIMEOUT` | Timeout counter value |

### Performance Events (EVENT_TYPE = 0x03)

| EVENT_CODE | Event | Payload |
|------------|-------|---------|
| 0x01 | `ARB_WAIT` | Wait cycles |
| 0x02 | `READ_LATENCY` | First beat latency |
| 0x03 | `WRITE_LATENCY` | First response latency |
| 0x04 | `THROUGHPUT` | Bytes transferred |

---

## Event Generation

### Configurable Events

Events can be enabled/disabled via APB registers:

| Register | Bit | Event Category |
|----------|-----|----------------|
| `MONBUS_CFG` | [0] | Transfer events |
| `MONBUS_CFG` | [1] | Error events |
| `MONBUS_CFG` | [2] | Performance events |
| `MONBUS_CFG` | [7:4] | Channel mask |

### Event Priority

When multiple events occur simultaneously:

1. Error events (highest priority)
2. Transfer completion events
3. Transfer start events
4. Performance events (lowest priority)

---

## Backpressure Handling

### Flow Control

- Events generated when `monbus_pkt_ready` is asserted
- If `monbus_pkt_ready` is low, events are queued in internal FIFO
- FIFO depth: 64 entries (configurable)
- Overflow behavior: Oldest events discarded, overflow counter incremented

### Recommendations

- Connect MonBus to FIFO with sufficient depth
- Monitor overflow counter in status register
- Size downstream FIFO based on expected event rate

---

## Typical MonBus Downstream

```
STREAM MonBus → MonBus FIFO → MonBus Arbiter → System Trace
                  (64 deep)    (multi-source)    Interface
```

---

## Example Event Sequence

A single-descriptor transfer generates these events:

```
Time    Event
----    -----
T0      KICKOFF     - Software kicks off channel
T1      DESC_FETCH  - Descriptor fetch initiated
T10     DESC_VALID  - Descriptor parsed successfully
T12     ARB_WAIT    - Waiting for data path grant (if applicable)
T15     READ_START  - AXI read burst initiated
T75     READ_DONE   - All source data read
T80     WRITE_START - AXI write burst initiated
T140    WRITE_DONE  - All data written, responses received
T141    COMPLETE    - Channel complete, back to IDLE
```

---

**Last Updated:** 2026-01-03
