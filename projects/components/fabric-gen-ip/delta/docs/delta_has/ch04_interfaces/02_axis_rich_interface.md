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

# AXI-Stream Rich Interface (TSTRB + AMBA5)

## Rich Master Interface (S_AXIS)

When `--strb-width N` and/or `--amba5` are used, the master interface adds the following signals in addition to the base set.

| Signal | Width | Direction | Presence | Description |
|--------|-------|-----------|----------|-------------|
| `s_axis_tstrb[m]` | `STRB_WIDTH` | Input | `--strb-width N` | Byte qualifier / strobe. Pass-through to `m_axis_tstrb`. |
| `s_axis_twakeup[m]` | 1 | Input | `--amba5` | Wakeup hint. May assert before `TVALID`. |
| `s_axis_tparity[m]` | `PW_WIDTH` | Input | `--amba5` | Parity sideband. Pass-through to `m_axis_tparity`. |

: Table 4.3: Rich Master Interface Additional Signals

## Rich Slave Interface (M_AXIS)

| Signal | Width | Direction | Presence | Description |
|--------|-------|-----------|----------|-------------|
| `m_axis_tstrb[s]` | `STRB_WIDTH` | Output | `--strb-width N` | Byte qualifier from the granted master. |
| `m_axis_twakeup[s]` | 1 | Output | `--amba5` | Wakeup hint. OR of all masters whose `TDEST` selects slave `s`. |
| `m_axis_tparity[s]` | `PW_WIDTH` | Output | `--amba5` | Parity sideband from the granted master. |

: Table 4.4: Rich Slave Interface Additional Signals

## TSTRB Semantics

- `TSTRB` is treated as an opaque byte-qualifier sideband.
- The crossbar forwards the granted master's `TSTRB` to the selected slave.
- Delta does not gate `TVALID` based on `TSTRB` or modify strobe bits.

## TWAKEUP Semantics

`TWAKEUP` is an AMBA 5 hint, not a handshake signal:

- A master may assert `s_axis_twakeup[m]` before `s_axis_tvalid[m]` to wake the target slave.
- The crossbar decodes `s_axis_tdest[m]` and ORs the hint to the indicated slave.
- `m_axis_twakeup[s]` may be high while `m_axis_tvalid[s]` is low.
- No grant is required for `TWAKEUP` steering.

## TPARITY Semantics

- `TPARITY` is treated as a pass-through sideband like `TUSER`.
- The width defaults to `DATA_WIDTH / 8` and can be overridden with `--parity-width M`.
- The crossbar forwards the granted master's `TPARITY` to the selected slave.

## Parameter Implications

| Option | Generated Parameter | Port Effect |
|--------|---------------------|-------------|
| `--strb-width N` | `STRB_WIDTH = N` | Adds `s_axis_tstrb` and `m_axis_tstrb` arrays. |
| `--amba5` | `PW_WIDTH = DATA_WIDTH/8` (default) | Adds `s_axis_twakeup/tparity` and `m_axis_twakeup/tparity` arrays. |
| `--amba5 --parity-width M` | `PW_WIDTH = M` | Overrides the default parity width. |

: Table 4.5: Rich-Flavor Parameter-to-Port Mapping
