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

# Write-to-Read Forward (`wr2rd_forward`)

**Module:** `wr2rd_forward.sv`
**Location:** `rtl/fub/`
**Category:** FUB
**Parent macro:** `axi_frontend_macro`
**Status:** v1 implemented

## Purpose

Write-to-read forwarding ("snarf") — when an AR's decoded address matches
an in-flight write that has not yet drained to DRAM, the read pulls data
straight from `axi_intake.w_buf` instead of issuing a DRAM read.

This preserves AXI per-ID in-order semantics for the common case where a
write is immediately followed by a read on the same line, without
serializing them through DRAM.

## Placement

Sits between `addr_mapper` and `rd_cmd_cam` on the AR path. For each
incoming AR:

1. Combinationally compares the decoded (rank, bank, row, col, burst_len)
   against every `wr_cmd_cam` slot's snapshot bus.
2. If a matching in-flight write exists AND its burst length matches AND
   it is full-beat (no byte-strobe gaps), redirect the AR to the
   forwarded path:
   - Do NOT push to `rd_cmd_cam`.
   - Emit `fwd_valid_o` with the write's `w_buf_ptr` and length so the
     read side can pull beats from `w_buf`.
   - Use the AR's own `axi_id` for the AXI rid echo.
3. Otherwise, pass the AR straight through to `rd_cmd_cam`.

## Design Notes

- **Last-write-wins**: if multiple writes match (programmer error or
  intentional double-write), the highest-slot-index match is taken —
  the most recently pushed write.
- **Pure flag-and-counter**, no FSM. Match lines are parallel comparators
  across the wr_cmd_cam snapshot bus.
- **Strb-coverage** in v1 is conservative: requires the AR's first beat
  AND every beat thereafter to be all-1 in the write's `strb_buf` (the
  write filled the entire read window). Partial overlaps fall through
  to DRAM.

## Memory Ordering

Forwarding preserves AXI per-ID in-order semantics — the snarf path
returns the same data the DRAM read would have, just earlier. Reads on
different IDs are unconstrained by AXI ordering so the snarf doesn't
violate any guarantees.

## Tests

Covered by the `axi_frontend_macro` integration tests
(`dv/tests/macro/test_axi_frontend_macro.py`) including the
`snarf_stream`, `last_write_wins`, and `issued_then_snarf` scenarios.
No FUB-level standalone test (the comparator + slot snapshot interface
is hard to mock without the full CAM).
