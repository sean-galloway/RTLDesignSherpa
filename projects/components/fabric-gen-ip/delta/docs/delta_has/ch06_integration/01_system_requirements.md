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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# System Requirements

## Toolchain Requirements

- **Synthesis:** Any SystemVerilog-2017-capable synthesis tool (Vivado, Yosys, Genus, etc.).
- **Simulation:** Any SystemVerilog simulator; cocotb is the planned verification framework.
- **Lint:** Verilator (`--lint-only`) is used for quick sanity checks.

## Runtime Requirements

- Single clock domain: all `s_axis_*` and `m_axis_*` interfaces use `aclk`.
- Active-low asynchronous reset: `aresetn` must be asserted at power-up.
- All upstream masters and downstream slaves must implement the AXI4-Stream handshake.

## Interface Assumptions

- Masters drive valid `TDEST` values (`0` to `NUM_SLAVES-1`).
- Slaves drive `m_axis_tready` independently.
- No master changes `TDEST` while waiting for a grant.
- `TID` and `TUSER` widths match the generated parameters.
- **Packets may interleave and reorder** (2026-10-19, owner direction,
  replacing the same-day "packets never interleave" assumption). Delta
  guarantees the order of flits within one packet and nothing between
  packets; an endpoint must not infer arrival order from send order. The
  tile's cells order their writes to RAPIDS by waiting for every credit back
  (RAPIDS MAS, Tile Packet Header, Ordering Across the Fabric, O4). Open:
  whether the AXIS and CXS plane ports still deliver one packet's flits
  together; RAPIDS's header-then-payload framing depends on it.

## Integration Checklist

- [ ] Confirm `DATA_WIDTH`, `NUM_MASTERS`, and `NUM_SLAVES` match the system.
- [ ] Confirm `DEST_WIDTH` and `ID_WIDTH` are wide enough for the generated module.
- [ ] Decide whether `TSTRB` or AMBA 5 sidebands are needed.
- [ ] Decide whether packet counters are needed (default on; use `--no-counters` to remove).
- [ ] Connect `aclk` and `aresetn` from the system.
- [ ] Verify downstream slaves can accept backpressure.
- [ ] Run `verilator --lint-only` on the generated RTL.
