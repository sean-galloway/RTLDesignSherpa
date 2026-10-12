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

# Parameters and Logic Implications

## Parameter Summary

| Parameter | Generated From | Logic Implication |
|-----------|----------------|-------------------|
| `DATA_WIDTH` | `--data-width` | Width of all `TDATA` and `TPARITY` default calculations. |
| `DEST_WIDTH` | `clog2(NUM_SLAVES)` | Width of `TDEST`; determines request decode comparison width. |
| `ID_WIDTH` | `clog2(NUM_MASTERS)` | Width of `TID`; pass-through only. |
| `USER_WIDTH` | `--user-width` | Width of `TUSER`; pass-through only. |
| `NUM_MASTERS` | `--masters` | Size of `s_axis_*` arrays and grant/request matrix columns. |
| `NUM_SLAVES` | `--slaves` | Size of `m_axis_*` arrays and grant/request matrix rows. |
| `STRB_WIDTH` | `--strb-width` | Width of `TSTRB`; adds mux ports when > 0. |
| `PW_WIDTH` | `--parity-width` or `DATA_WIDTH/8` | Width of `TPARITY`; adds mux ports when `--amba5` is set. |

: Table 4.1: Parameter-to-Logic Mapping

## Width Calculations

The generator computes:

```python
dest_width = max(1, ceil(log2(num_slaves)))
id_width   = max(1, ceil(log2(num_masters)))
```

A single master or slave still gets a 1-bit width to avoid zero-width signals.

## Parameter Interaction

- `STRB_WIDTH == 0` omits `TSTRB` entirely.
- `PW_WIDTH` is meaningful only when `--amba5` is set; otherwise `TPARITY` and `TWAKEUP` ports are not generated.
- `--parity-width` without `--amba5` is rejected by the CLI parser.

## RTL Constants

The generator uses `generate`/`genvar` loops sized by `NUM_MASTERS` and `NUM_SLAVES`. Changing these parameters after generation requires regenerating the module; the parameter is set at generation time, not truly configurable post-generation. This is intentional: it allows the synthesizer to optimize the fixed-size structure.
