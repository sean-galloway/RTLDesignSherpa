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

# Module Structure

## Generated File

The generator produces one file per configuration:

```
delta_axis_flat_MxN.sv
```

where `M` is `NUM_MASTERS` and `N` is `NUM_SLAVES`.

## Module Header

The module begins with parameters and port declarations. The exact port list depends on the selected richness options.

### Base Flavor Header

```systemverilog
module delta_axis_flat_4x16 #(
    parameter int DATA_WIDTH  = 64,
    parameter int DEST_WIDTH  = 4,
    parameter int ID_WIDTH    = 2,
    parameter int USER_WIDTH  = 1,
    parameter int NUM_MASTERS = 4,
    parameter int NUM_SLAVES  = 16
)(
    input  logic aclk,
    input  logic aresetn,
    // s_axis and m_axis base ports...
);
```

### Rich Flavor Additions

When `--strb-width` is used, `STRB_WIDTH` is added to the parameter list and `s_axis_tstrb`/`m_axis_tstrb` are added to the ports.

When `--amba5` is used, the check-width parameters `TDATACHK_W`, `TIDCHK_W`, `TDESTCHK_W` and `TUSERCHK_W` are added, plus `TSTRBCHK_W` with `--strb-width`. Each is derived from its payload width. The ports gain `s_/m_axis_twakeup`, the nine IHI 0051B check signals per side (`*_axis_tdatachk` ... `*_axis_twakeupchk`), and the sticky `s_parity_error[NUM_MASTERS]` / `m_parity_error[NUM_SLAVES]`. The module then instantiates `rtl/common/dataint_parity`, so its filelist must `-f` include `rtl/common/filelists/dataint_parity.f`.

## Internal Organization

Inside the module, the generator emits sections in this order:

1. Header comment with configuration.
2. Request decode.
3. Per-slave round-robin arbiter.
4. Crossbar data mux.
5. TREADY steering.
6. TWAKEUP steering (if enabled).
7. Interface check signals (if `--amba5`).
8. Performance counters (unless disabled).
9. Assertions (under `ifdef FORMAL`).

## Filelist

The checked-in RTL includes `$REPO_ROOT`-relative filelists under `rtl/filelists/` for use with simulation and synthesis flows.
