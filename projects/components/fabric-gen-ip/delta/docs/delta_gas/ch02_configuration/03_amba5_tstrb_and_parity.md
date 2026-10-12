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

# AMBA 5, TSTRB, and Parity Options

## TSTRB byte qualifiers

By default Delta omits `TSTRB` to match the common AXI-Stream use case where every byte is valid. To emit byte-qualifier ports:

```bash
python3 delta_generator.py --masters 2 --slaves 4 --strb-width 8
```

The generator adds `s_axis_tstrb` and `m_axis_tstrb` arrays and muxes them alongside `TDATA`.

## AMBA 5 sidebands (`--amba5`)

When `--amba5` is set, the generator adds two AMBA 5 signals:

- `s_axis_twakeup[NUM_MASTERS]` and `m_axis_twakeup[NUM_SLAVES]` — wakeup hints.
- `s_axis_tparity[NUM_MASTERS][PW_WIDTH-1:0]` and `m_axis_tparity[NUM_SLAVES][PW_WIDTH-1:0]` — parity vectors.

### TWAKEUP steering

`TWAKEUP` is treated as a hint that may arrive before `TVALID`. The generator decodes it directly from `TDEST` without waiting for a grant:

```systemverilog
m_axis_twakeup[s] = OR over all m of (s_axis_twakeup[m] && s_axis_tdest[m] == s);
```

### TPARITY routing

`TPARITY` is routed with the same grant-based mux as `TDATA`. Parity is **not** checked or regenerated inside the crossbar; it is assumed to be generated and checked by the endpoints. If end-to-end parity protection is required, the endpoints must use a consistent algorithm and width.

## Parity width default

If `--amba5` is set and `--parity-width` is 0, the generator defaults to:

```python
parity_w = data_width // 8
```

This matches one parity bit per byte. A custom width may be requested if the system uses a different parity granularity.
