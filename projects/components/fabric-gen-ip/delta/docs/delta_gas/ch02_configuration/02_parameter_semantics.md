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

# Parameter Semantics

## Generation-time parameters

These are fixed in the emitted module name and structure.

| Parameter | Effect in emitted RTL |
|-----------|-----------------------|
| `num_masters` | Number of `s_axis_*` input interfaces; sets `NUM_MASTERS` and `TID` width. |
| `num_slaves` | Number of `m_axis_*` output interfaces; sets `NUM_SLAVES` and `TDEST` width. |
| `data_width` | `TDATA` width; sets `DATA_WIDTH`. |
| `user_width` | `TUSER` width; sets `USER_WIDTH`. |
| `strb_width` | If > 0, adds `TSTRB` ports and sets `STRB_WIDTH`; otherwise omits them. |
| `amba5` | Adds `TWAKEUP`, the IHI 0051B ch. 5 check signals and the `s_/m_parity_error` flags; adds the derived check-width parameters. |
| `registered_outputs` | Reserved for future output-register insertion; currently affects header comments. |
| `arbiter_type` | Reserved for future arbiter selection; currently only round-robin is emitted. |
| `add_performance_counters` | Adds 32-bit packet counters per master and slave. |

: Generation-Time Parameters

## Elaboration-time parameters

The generated flat crossbar exposes the following parameters:

```systemverilog
module delta_axis_flat_2x4 #(
    parameter int DATA_WIDTH = 64,
    parameter int DEST_WIDTH = 2,
    parameter int ID_WIDTH   = 1,
    parameter int USER_WIDTH = 1,
    parameter int NUM_MASTERS = 2,
    parameter int NUM_SLAVES  = 4
) (
```

When `strb_width > 0`, `STRB_WIDTH` is added. When `amba5=True`, `TDATACHK_W`, `TIDCHK_W`, `TDESTCHK_W` and `TUSERCHK_W` are added, plus `TSTRBCHK_W` with TSTRB. Each defaults to an expression of its payload width, so leave them at their defaults.

| Parameter | Typical use |
|-----------|-------------|
| `DATA_WIDTH` | Match the datapath width of the surrounding AXI-Stream network. |
| `DEST_WIDTH` | Wide enough to encode `NUM_SLAVES - 1`. |
| `ID_WIDTH` | Wide enough to encode `NUM_MASTERS - 1`. |
| `USER_WIDTH` | Carry sideband metadata alongside each beat. |

: Elaboration-Time Parameters

The master and slave counts are **not** elaboration-time parameters. A 2×4 module cannot be instantiated as 2×8. Generate a new module instead.
