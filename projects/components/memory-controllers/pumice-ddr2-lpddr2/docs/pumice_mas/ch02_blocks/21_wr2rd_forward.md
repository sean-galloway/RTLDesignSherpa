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

# Write-to-Read Forward — RETIRED as a standalone block

**Status:** RETIRED. There is no `wr2rd_forward.sv` in the live RTL.
**Replaced by:** the **snarf mover inside `pumice_wr_data_cam`** (see §17,
the Write Data Path chapter).
**Probe driver:** `pumice_rd_intake` (the snarf probe on the AR path).

## Why it was retired

The rearchitected AXI4 interface (`pumice_axi4_ifc`) folded write-to-read
forwarding into the write CAM rather than keeping it as a separate FUB on
the AR path. The old `wr2rd_forward` block sat between `addr_mapper` and
`rd_cmd_cam` and compared each AR against a `wr_cmd_cam` snapshot bus;
that snapshot bus, the standalone comparator, and the separate `w_buf`
storage it read from no longer exist. Forwarding is now a native operation
of `pumice_wr_data_cam`, which already holds the pending writes and their
burst data in its SRAM.

## Where forwarding lives now

Write-to-read forwarding ("snarf") is the **snarf mover** of
`pumice_wr_data_cam`. The flow is:

1. `pumice_rd_intake` presents an incoming AR's decoded key
   `{bank, row, col}` plus its AXI id and `arlen` on the CAM's
   `snarf_probe_*` port.
2. `pumice_wr_data_cam` combinationally searches its entries and asserts
   `snarf_hit_o` for a **youngest** match, subject to the safe-case
   restrictions.
3. On `snarf_accept_i`, the matched slot is queued into the snarf request
   FIFO and the snarf mover streams the write's SRAM beats back on
   `snarf_rd_*` (non-destructively — the write still drains to DRAM
   normally). Otherwise the read takes the DRAM miss path through
   `pumice_rd_cmd_cam` (§18).

## Restrictions (narrower than the old block)

The live snarf is limited to the safe case — a write is snarfable only if
**all three** hold:

- **Unscheduled** (`!r_sched`): a scheduled write is draining/evicting to
  DRAM, so its CAM data is racy.
- **Same AXI id**: same-id write-before-read is the only AXI-ordered case
  where the read is *required* to see the write. Cross-id reads have no
  ordering guarantee and take the DRAM path.
- **Same burst length** (`arlen == BL-1`): every admitted write is exactly
  `BL` beats (ragged bursts are rejected in `pumice_wr_intake`), so a short
  or long read cannot snarf a full-BL write.

The match must also be fill-complete (`r_fdone`); among candidates the
**youngest** wins (latest data). This differs from the old block's
"last-write-wins by highest slot index, any matching id, conservative
all-1 strb-coverage" policy — the live rule is youngest + same-id +
same-BL + unscheduled.

## Memory Ordering

Forwarding preserves AXI per-ID in-order semantics: the snarf path returns
the same data a DRAM read would have, just earlier. Because it is
restricted to same-id matches, it never forwards across an unordered
cross-id pair.

## Tests

Covered by the `pumice_wr_data_cam` FUB test and the `pumice_axi4_ifc`
integration tests (snarf stream, snarf-vs-DRAM-path selection, and the
same-id / same-BL / unscheduled exclusion scenarios). See §17 for the
detailed test plan.
