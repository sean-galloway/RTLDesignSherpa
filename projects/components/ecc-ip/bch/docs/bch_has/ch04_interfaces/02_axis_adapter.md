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

Generated at an end when its `*_IF` parameter is `"AXIS"`. It mirrors the
posture of the reed-solomon AXI-Stream adapter (PRD D9 direction) but is not
yet designed; the table below is the target contract **TBD / D9**.

The adapter is the house `axis4_slave` (intake) or `axis4_master` (outlet)
timing wrapper with the core's stream mapped onto the AXI-Stream signals.

| AXIS signal | Core signal | Notes |
|---|---|---|
| `TVALID` / `TREADY` | `valid` / `ready` | one-to-one |
| `TDATA[B-1:0]` | `data` | B bits per beat |
| `TKEEP[B/8-1:0]` or per-bit | `keep` | byte keep or bit mask; the BCH-specific partial-beat encoding is part of D9 |
| `TLAST` | `last` | the block boundary |
| `TUSER` (intake, decoder) | `in_erase[B-1:0]` | erasure flags, one per bit lane, only when `ENABLE_ERASURES = 1`; otherwise the consumer's `TUSER` passes through the intake unused |
| `TUSER` (outlet, decoder) | status | `{frame_err, uncorrectable, corrected[..], ok}`, valid with `TLAST` |
| `TID`, `TDEST` | -- | passed through unchanged from intake to outlet when both ends are AXIS; tied off otherwise |

: Table 4.4: AXI-Stream mapping (target)

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
