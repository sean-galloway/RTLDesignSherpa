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

# AXI Monitor Reporter — Completion Cone

**Module:** `axi_monitor_reporter_compl.sv`
**Location:** `rtl/amba/monitor/`
**Status:** Production Ready

---

## Overview

The AXI Monitor Reporter Completion Cone is the completion-packet detection sub-block of `axi_monitor_reporter`. It scans the outstanding-transaction table for slots that have reached the `TRANS_COMPLETE` state but have not yet been reported, priority-encodes the first such slot, and emits the fields for a `PktTypeCompletion` MonBus packet. It was split out of the monolithic reporter so integrators who do not need completion packets can drop it with `ENABLE_COMPL_LOGIC=0` and pay zero LUT cost for the per-slot scan and priority encoder. The block is purely combinational.

### Key Features

- Scans the shared transaction table for unreported `TRANS_COMPLETE` slots
- First-match priority encoder selects one slot per cycle
- Emits `PktTypeCompletion` packet fields with event code `EVT_TRANS_COMPLETE`
- Runtime-gated by `cfg_compl_enable`; compile-time removable via the parent's `ENABLE_COMPL_LOGIC`
- Reports the selected slot index (`sel_idx`) back to the top reporter for `event_reported` feedback
- Pure combinational — all state (table, `event_reported`) lives in the top reporter

---

## Module Purpose

The transaction manager tracks every outstanding AXI transaction and marks a slot `TRANS_COMPLETE` when it finishes cleanly. Someone must turn those completions into MonBus packets exactly once each. This cone does the detect-and-select half of that job: it finds the completed-but-unreported slots, picks the first, and hands the packet fields plus the chosen slot index up to the top reporter, which pushes the packet into the shared MonBus FIFO and sets the slot's `event_reported` bit so it is not emitted again. Factoring it into its own module means the (non-trivial) MAX_TRANSACTIONS-wide scan and encoder synthesize only when completion reporting is actually wanted.

**Use Cases:**
- Emitting one completion packet per successfully-finished AXI transaction
- Completion-tracking test/verification configurations
- Transaction-throughput accounting on the MonBus

**Key Benefit:** Isolates the completion scan/encoder so it can be compiled out (`ENABLE_COMPL_LOGIC=0`) for zero area when completion packets are not needed.

---

## Parameters

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| MAX_TRANSACTIONS | int | 16 | Depth of the shared transaction table scanned |
| IDX_W | int | `$clog2(MAX_TRANSACTIONS)` | Width of the selected-slot index |

---

## Port Groups

### Inputs (shared monitor state)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| trans_table | input | bus_transaction_t × MAX_TRANSACTIONS | The outstanding-transaction table |
| event_reported | input | MAX_TRANSACTIONS | Per-slot "already reported" mask (from the top reporter) |
| cfg_compl_enable | input | 1 | Runtime enable for completion reporting |

### Outputs (packet fields to the top reporter)

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| pkt_valid | output | 1 | A completed-unreported slot was found this cycle |
| pkt_type | output | 4 | Packet type = `PktTypeCompletion` |
| pkt_event_code | output | 8 | Event code = `EVT_TRANS_COMPLETE` |
| pkt_channel | output | 9 | Channel id `{3'b0, slot.channel[5:0]}` |
| pkt_data | output | 64 | Slot address, zero-padded to 64 bits |
| sel_idx | output | IDX_W | Index of the selected slot (for `event_reported` feedback) |

---

## Functional Description

### Completion Scan

For every slot in `trans_table`, the slot qualifies as a completion event when it is `valid`, its `event_reported` bit is clear, its `state == TRANS_COMPLETE`, and `cfg_compl_enable` is set. All qualifying slots are collected into a one-hot-per-bit `w_events` vector.

### First-Match Selection

A second loop scans `w_events` from index 0 upward and latches the first set bit into `w_sel`, asserting `w_has_event`. The `WIDTHTRUNC` lint is locally waived where the loop index is narrowed to `IDX_W`. This gives strict low-index-first priority so exactly one completion is emitted per cycle even when several slots complete together; the rest are picked up on subsequent cycles once the winner is marked reported.

### Emitted Fields

- `pkt_valid` = `w_has_event`
- `sel_idx` = `w_sel` (tells the top reporter which slot to mark reported)
- `pkt_type` = `PktTypeCompletion`
- `pkt_event_code` = `EVT_TRANS_COMPLETE`
- `pkt_channel` = `{3'b0, trans_table[w_sel].channel[5:0]}`
- `pkt_data` = `pad_address(trans_table[w_sel].addr)` — the 32-bit slot address zero-extended to 64 bits

### Ownership of State

The block holds no state of its own. The transaction table and the `event_reported` feedback mask both live in the top reporter (`axi_monitor_reporter`), which consumes `sel_idx` to set the reported bit after the packet is accepted. Keeping this cone combinational lets several such cones (completion, error, timeout, ...) share the same table snapshot each cycle.

---

## Usage Example

```systemverilog
// Instantiated inside axi_monitor_reporter, gated by ENABLE_COMPL_LOGIC.
axi_monitor_reporter_compl #(
    .MAX_TRANSACTIONS (MAX_TRANSACTIONS)
) u_compl (
    .trans_table     (trans_table),
    .event_reported  (event_reported),
    .cfg_compl_enable(cfg_compl_enable),

    .pkt_valid       (compl_valid),
    .pkt_type        (compl_type),
    .pkt_event_code  (compl_event_code),
    .pkt_channel     (compl_channel),
    .pkt_data        (compl_data),
    .sel_idx         (compl_sel_idx)   // top reporter sets event_reported[compl_sel_idx]
);
```

---

## Design Notes

### Compile-Out Path

The parent instantiates this cone under `ENABLE_COMPL_LOGIC`. Setting it to 0 removes the MAX_TRANSACTIONS-wide qualifier scan and priority encoder entirely, so a monitor build that never reports completions pays no LUT cost for them. `cfg_compl_enable` is the softer runtime mask when the logic is present.

### Combinational by Design

All state lives upstream; this block is a pure combinational detect-and-select cone. Multiple packet cones can therefore examine the same table each cycle without duplicating storage, and the top reporter arbitrates which one wins the MonBus this cycle.

### One Packet Per Cycle

The strict first-match encoder emits at most one completion per cycle. Simultaneous completions are serialized across cycles as each winner is marked reported.

---

## Related Modules

### Used By
- **axi_monitor_reporter.sv** - Top reporter that pushes the packet into the MonBus FIFO and drives `event_reported`

### Uses
- **monitor_common_pkg** - `PktTypeCompletion`, `TRANS_COMPLETE`, `bus_transaction_t`
- **monitor_amba4_pkg** - `EVT_TRANS_COMPLETE` event code

### See Also
- **axi_monitor_reporter_error.sv** - Error/orphan detection cone (sibling sub-block)
- **axi_monitor_reporter_debug.sv** - State-change debug emitter (sibling sub-block)
- **axi_monitor_base.sv** - The monitor scaffold that houses trans_mgr + reporter

---

## References

### Source Code
- RTL: `rtl/amba/monitor/axi_monitor_reporter_compl.sv`

### Documentation
- Packet format: `docs/markdown/rtl-amba/includes/monitor_package_spec.md`
- Monitor base: `docs/markdown/rtl-amba/axi_monitor_base.md`
- Known issues: `rtl/amba/KNOWN_ISSUES/axi_monitor_reporter.md`

---

**Last Updated:** 2026-07-15

---

## Navigation

- [Back to Shared Infrastructure Index](../_book_monitor_index.md)
- [Back to rtl-amba Index](../index.md)
