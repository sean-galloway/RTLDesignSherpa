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

# AXI-Stream Adapter

Generated at an end when its `*_IF` parameter is `"AXIS"`. It is the house
`axis4_slave` (intake) or `axis4_master` (outlet) timing wrapper -- the same
modules the bridge uses at its AXI-Stream ports -- with the core's stream
mapped onto the AXI-Stream signals as follows.

| AXIS signal | Core signal | Notes |
|---|---|---|
| `TVALID` / `TREADY` | `valid` / `ready` | one-to-one |
| `TDATA[DATA_WIDTH-1:0]` | `data` | S symbols per beat |
| `TKEEP[S*m/8-1:0]` | `keep` | byte keep; symbols are whole bytes when m = 8, else `TKEEP` is per symbol byte-group and `TSTRB` is not used |
| `TLAST` | `last` | the block boundary |
| `TUSER` (intake, decoder) | `in_erasure[S-1:0]` | erasure flags, one per symbol lane, only when `ERASURE_SUPPORT = 1`; otherwise the consumer's `TUSER` passes through the intake unused |
| `TUSER` (outlet, decoder) | status | `{frame_err, uncorrectable, corrected[..], ok}`, valid with `TLAST` |
| `TID`, `TDEST` | -- | passed through unchanged from intake to outlet when both ends are AXIS; tied off otherwise |

: Table 4.4: AXI-Stream mapping

## Parameters

| Parameter | Default | Meaning |
|---|---|---|
| `AXIS_SKID_DEPTH` | 2 | skid depth in the wrapper (2..8) |
| `AXIS_ID_WIDTH`, `AXIS_DEST_WIDTH` | 0 | pass-through sideband widths |
| `AXIS_MONITOR` | 0 | 1 selects the `_monlite` wrapper variant, which attaches `axis_monitor_lite` to the port and emits onto the monitor bus |

: Table 4.5: AXI-Stream adapter parameters

## Behaviour

The adapter adds no protocol semantics: TLAST is the block boundary the core
requires, and the rate change is visible as more beats out than in on the
encoder (or fewer on the decoder). A stream that arrives without TLAST at
block boundaries cannot be decoded and is reported as a framing error on
every block.

## Erasure sideband (decoder intake, `ERASURE_SUPPORT = 1`)

The decoder wrapper takes a per-beat `in_erasure[S-1:0]` port, one flag per
symbol lane, valid with the beat. The flags are spliced ABOVE the consumer's
`TUSER` through the intake skid -- the skid is built with
`AXIS_USER_WIDTH = AXIS_USER_WIDTH + S` (a zero consumer width still costs
one guard bit) and the core-facing side slices the top S bits back off -- so
the flags stay beat-aligned with their data under any backpressure, which a
sideband registered outside the skid cannot guarantee. With
`ERASURE_SUPPORT = 0` the port does not exist and the intake is the
pre-erasure wrapper, bit for bit.

One integration rule this forces: the flags ride `TUSER` through the skid,
so any configuration that zeroes `AXIS_ID_WIDTH` or `AXIS_DEST_WIDTH` must
run the fixed `axis4_slave` (per-field tuser unpack; amba BUG-038, the
8-branch concatenation shifted tuser right whenever a zero-width guard bit
preceded it). The DV grid sweeps `(ID, DEST) in {(4, 2), (0, 0)}` for both
wrappers.
