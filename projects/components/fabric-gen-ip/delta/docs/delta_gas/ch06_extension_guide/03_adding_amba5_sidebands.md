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

# Adding AMBA 5 Sidebands

The current AMBA 5 support covers `TWAKEUP` and `TPARITY`. To add more AMBA 5 sidebands:

1. Add the new signal to `DeltaConfig` (e.g., a width field).
2. In `DeltaFlatCrossbar.__init__`, add the new port declarations when `amba5` is enabled.
3. Add routing logic in a new `generate_*_logic()` method.
4. Call the new method from `verilog()`.
5. Update the DV suite to exercise the new sideband.

## TWAKEUP design note

`TWAKEUP` is a hint, not a data beat. It is routed by `TDEST` without arbitration because it may precede `TVALID`. If a future sideband requires grant-based routing, follow the `TPARITY` pattern in `generate_crossbar_mux()`.

## TPARITY design note

The generator routes `TPARITY` with the same grant as `TDATA`. It does not check parity inside the crossbar. If end-to-end protection is required, add parity generation/checking at the endpoints or extend the crossbar to compute parity on every hop.
