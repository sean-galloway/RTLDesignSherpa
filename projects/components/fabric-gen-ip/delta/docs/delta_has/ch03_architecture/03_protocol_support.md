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

# Protocol Support

## AXI4-Stream Base Flavor

The default generated crossbar implements the standard AXI4-Stream signal set:

- `TDATA` — data payload
- `TVALID` / `TREADY` — handshake
- `TLAST` — packet boundary
- `TDEST` — destination slave index
- `TID` — transaction/master ID (pass-through)
- `TUSER` — user sideband (pass-through)

This is the byte-identical default; no sideband options are enabled unless requested.

## Optional TSTRB Byte Qualifiers

The `--strb-width N` option adds `TSTRB` to every master and slave interface. `TSTRB` is treated as a pass-through sideband: the mux forwards the granted master's `TSTRB` to the selected slave. Delta does not interpret or modify strobe bits.

## Optional AMBA 5 Sidebands

The `--amba5` option adds two AMBA 5 signals:

- `TWAKEUP` — wakeup hint, decoded from `TDEST` and ORed per slave.
- `TPARITY` — parity sideband, treated as pass-through like `TUSER`.

The parity width defaults to `DATA_WIDTH / 8` and can be overridden with `--parity-width M`. The generated ports port-match the `rtl/amba/axis5/*` conventions.

## What Delta Does Not Support

Delta is intentionally AXI4-Stream only. It does **not** support:

- AXI4 memory-mapped transactions (AW/AR/W/B/R channels).
- AXI4-Lite register-mapped access.
- APB transfers.
- Burst lengths, address phases, or memory attributes.
- Dynamic reconfiguration of the crossbar dimensions.

For memory-mapped fabrics, use the sibling `bridge` or `apbx-xbar` components.

## Protocol Compliance Summary

| Feature | Base Flavor | Rich Flavor | Notes |
|---------|-------------|-------------|-------|
| TVALID/TREADY handshake | Yes | Yes | Standard AXI4-Stream |
| TLAST packet boundary | Yes | Yes | Grant release on TLAST |
| TDEST routing | Yes | Yes | Direct slave index |
| TID/TUSER pass-through | Yes | Yes | Unmodified |
| TSTRB | No | Yes | `--strb-width N` |
| TWAKEUP | No | Yes | `--amba5` |
| TPARITY | No | Yes | `--amba5 [--parity-width M]` |

: Table 3.2: Protocol Support Matrix
