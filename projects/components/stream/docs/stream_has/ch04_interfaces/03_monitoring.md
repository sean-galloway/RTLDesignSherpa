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

STREAM provides a unified Monitor Bus (MonBus) interface for debug and performance monitoring. This interface streams event packets (128-bit) with paired 64-bit side-band timestamps, capturing key operational events from all internal blocks.

---

## Signal Summary

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `monbus_pkt_valid` | Output | 1 | Packet valid |
| `monbus_pkt_ready` | Input | 1 | Downstream ready |
| `monbus_pkt_data` | Output | 128 | Packet data (protocol-independent monitor packet) |
| `monbus_ts_data` | Output | 64 | Side-band timestamp (cycle count at packet capture) |

---

## Packet Format

The 128-bit MonBus packet and 64-bit timestamp are paired atomically and transmitted as a 192-bit group through AXI-Lite skid buffering. See the canonical packet specification at `docs/markdown/RTLAmba/includes/monitor_package_spec.md` for complete field definitions.

| Bits | Field | Description |
|------|-------|-------------|
| [63:56] | `SUBSYSTEM_ID` | STREAM subsystem identifier |
| [55:48] | `EVENT_TYPE` | Event category |
| [47:40] | `EVENT_CODE` | Specific event within category |
| [39:32] | `CHANNEL_ID` | Associated channel (0-7) |
| [31:0] | `PAYLOAD` | Event-specific data |

---

## Monitoring Architecture

### Descriptor Path Monitoring (Both Ends)

STREAM monitors the descriptor fetch path at **both ends** for observability:

1. **Descriptor Fetch Master (Agent ID 8):** Monitors the AXI4 master that fetches descriptors from system memory
2. **Descriptor Consume Side (Agent ID 48 + channel):** Monitors when the scheduler consumes the descriptor for processing

This dual-end monitoring allows software to attribute descriptor path stalls to either fetch delay (master side) or consume delay (slave side), enabling faster root-cause analysis.

### Global Monitor Enable Methodology

All internal monitors are gated by:
- **Global SV parameter:** `USE_MONITOR` (default: enabled for analysis, disabled for area-optimized builds)
- **Per-port SV parameters:** Individual monitor enable for each monitored port
- **APB runtime configuration:** Masks for enabling/disabling packet types at run time

---

## Event Types

STREAM uses the unified MonBus event categorization defined in `docs/markdown/RTLAmba/includes/monitor_package_spec.md`:
- **Error events (Type 0x0):** Protocol violations, timeouts, invalid descriptors
- **Completion events (Type 0x1):** Successful transfer completion, descriptor processed
- **Performance events (Type 0x4):** Latency metrics, throughput data
- **Protocol-specific events:** AXI address-match, debug traces

All STREAM events use **Unit ID = 1** and channel-specific **Agent IDs** for the source block (descriptor engine, scheduler, AXI monitor, etc.).

Do not re-state the 128-bit packet layout here — refer to the canonical specification for field definitions and bit assignments.

---

## Event Configuration

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
