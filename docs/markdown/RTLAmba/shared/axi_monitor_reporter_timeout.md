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

# AXI Monitor Reporter — Timeout Packets

**Module:** `axi_monitor_reporter_timeout.sv`
**Location:** `rtl/amba/shared/`
**Status:** Production Ready

---

## Overview

The `axi_monitor_reporter_timeout` module is the timeout-packet emitter for the AXI/AXIL monitor family. It is one of the per-packet-type sub-blocks dispatched by the top-level `axi_monitor_reporter`. It is a pure combinational cone that scans the transaction table for unreported error slots the timeout detector has flagged, priority-encodes the first match, and drives the corresponding `PktTypeTimeout` packet fields.

The block was split out of the original monolithic reporter so integrators can drop it (`ENABLE_TIMEOUT_LOGIC=0`).

### Key Features

- Pure combinational detection (no internal state)
- Scans for valid, unreported, error-state slots flagged as timed out
- Priority-encodes the first matching slot
- Emits the packet's event code, channel, and address directly from the table
- Exposes the selected slot index (`sel_idx`) for the top reporter's mark-reported feedback
- Shares the `timeout_detected` vector with the error sub-block to avoid double-reporting

---

## Module Purpose

When a transaction stalls, the `axi_monitor_timeout` block asserts a per-slot `timeout_detected` bit and the transaction manager moves that slot into the `TRANS_ERROR` state. This reporter block turns that condition into a MonBus packet: it finds the first slot that is valid, in error, timed out, and not yet reported, and emits a timeout packet describing it (event code, channel, and address).

**Use Cases:**
- Reporting stuck AXI transactions (missing R/B response, hung handshake)
- Surfacing protocol hangs to a host IRQ handler for recovery
- Regression detection of deadlock or backpressure faults
- Correlating a timeout with the offending address and channel

**Key Benefit:** Zero-state, low-cost detection that shares its `timeout_detected` and `event_reported` vectors with the error emitter, guaranteeing each stuck transaction is reported exactly once.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `MAX_TRANSACTIONS` | int | 16 | Number of transaction slots scanned |
| `IDX_W` | int | `$clog2(MAX_TRANSACTIONS)` | Derived width of the selected-slot index |

---

## Port Groups

### Inputs

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `trans_table` | input | `bus_transaction_t [MAX_TRANSACTIONS]` | Live outstanding-transaction table (valid, state, event_code, channel, addr) |
| `event_reported` | input | MAX_TRANSACTIONS | Per-slot bit indicating the slot's event was already emitted (suppresses re-reporting) |
| `timeout_detected` | input | MAX_TRANSACTIONS | Per-slot timeout flags from `axi_monitor_timeout` |
| `cfg_timeout_enable` | input | 1 | Enable timeout packet generation |

### Packet Output

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `pkt_valid` | output | 1 | A timeout packet is available (a matching slot was found) |
| `pkt_type` | output | 4 | Packet type — constant `PktTypeTimeout` (4'h3) |
| `pkt_event_code` | output | 8 | Event code taken from the selected slot's `event_code.raw_code` |
| `pkt_channel` | output | 9 | Channel of the selected slot (low 6 bits, zero-extended) |
| `pkt_data` | output | 64 | Zero-extended address of the selected slot |
| `sel_idx` | output | IDX_W | Index of the selected slot, returned to the top reporter for mark-reported feedback |

---

## Functional Description

### Candidate Detection

A combinational loop builds a one-hot-eligible mask `w_events`: a slot qualifies when it is `valid`, its `event_reported` bit is clear, its state is `TRANS_ERROR`, timeout reporting is enabled (`cfg_timeout_enable`), and the slot's `timeout_detected` bit is set. This intersection ensures only genuinely-timed-out, not-yet-reported error slots are candidates.

### Priority Encoding

A second loop scans `w_events` from index 0 upward and latches the first asserted slot into `w_sel`, asserting `w_has_event`. This gives a deterministic, lowest-index-first selection.

### Output Assignment

The outputs are pure continuous assignments off the selected slot:

- `pkt_valid = w_has_event`
- `sel_idx = w_sel`
- `pkt_type = PktTypeTimeout`
- `pkt_event_code = trans_table[w_sel].event_code.raw_code`
- `pkt_channel = {3'b0, trans_table[w_sel].channel[5:0]}`
- `pkt_data = pad_address(trans_table[w_sel].addr)` (zero-extended to 64 bits)

### No Double-Reporting

The error sub-block masks the same `timeout_detected` slots, so a stuck transaction that is reported as a timeout here is not also reported as a plain error. The top reporter uses `sel_idx` to set the slot's `event_reported` bit, retiring the candidate.

---

## Usage Example

This block is instantiated inside `axi_monitor_reporter`, not by users directly:

```systemverilog
axi_monitor_reporter_timeout #(
    .MAX_TRANSACTIONS (MAX_TRANSACTIONS)
) u_reporter_timeout (
    .trans_table        (w_trans_table),
    .event_reported     (w_event_reported),
    .timeout_detected   (w_timeout_detected),
    .cfg_timeout_enable (cfg_timeout_enable),

    .pkt_valid          (w_timeout_pkt_valid),
    .pkt_type           (w_timeout_pkt_type),
    .pkt_event_code     (w_timeout_pkt_event_code),
    .pkt_channel        (w_timeout_pkt_channel),
    .pkt_data           (w_timeout_pkt_data),
    .sel_idx            (w_timeout_sel_idx)
);
```

---

## Design Notes

### Pure Combinational

The block holds no state; all edge-tracking and mark-reported bookkeeping lives in the top reporter. This keeps the timeout cone cheap and lets the top reporter arbitrate timeout packets against the other sub-emitters within one cycle.

### Event Code Comes From the Slot

`pkt_event_code` is not a fixed constant — it is the slot's captured `event_code.raw_code`, so the packet carries the specific timeout reason recorded when the transaction manager moved the slot to `TRANS_ERROR`.

### Shared Vectors Are Load-Bearing

Correct single-reporting depends on the top reporter driving `event_reported` and the timeout detector driving `timeout_detected` consistently. Historically, a missing `event_reported` feedback path caused transaction-table exhaustion; that feedback is now in place (see `rtl/amba/KNOWN_ISSUES/axi_monitor_reporter.md`).

---

## Related Modules

### Used By
- **axi_monitor_reporter.sv** — instantiates this block as its timeout-packet sub-emitter
- **axi_monitor_base.sv** — top-level monitor scaffold

### Uses
- **monitor_common_pkg** — `PktTypeTimeout`, `bus_transaction_t`, `TRANS_ERROR`
- **monitor_amba4_pkg** — AMBA event-code definitions
- (No sequential logic — no reset macros required)

### See Also
- **axi_monitor_timeout.sv** — produces the `timeout_detected` vector consumed here
- **axi_monitor_reporter_perf.sv** — performance packet emitter (sibling)
- **axi_monitor_reporter_threshold.sv** — threshold packet emitter (sibling)

---

## References

### Source Code
- RTL: `rtl/amba/shared/axi_monitor_reporter_timeout.sv`
- Parent: `rtl/amba/shared/axi_monitor_reporter.sv`
- Packages: `rtl/amba/includes/monitor_common_pkg.sv`, `rtl/amba/includes/monitor_amba4_pkg.sv`

### Documentation
- Architecture: `docs/markdown/RTLAmba/shared/README.md`
- Monitor Base: `docs/markdown/RTLAmba/shared/axi_monitor_base.md`
- Known Issues: `rtl/amba/KNOWN_ISSUES/axi_monitor_reporter.md`
- Packet Format: `docs/markdown/RTLAmba/includes/monitor_package_spec.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](README.md)
- [Back to RTLAmba Index](../index.md)
