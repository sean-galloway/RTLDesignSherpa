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

The current AMBA 5 support covers `TWAKEUP` and the full IHI 0051B chapter 5 check-signal set (`TDATACHK`, `TSTRBCHK`, `TLASTCHK`, `TIDCHK`, `TDESTCHK`, `TUSERCHK`, `TVALIDCHK`, `TREADYCHK`, `TWAKEUPCHK`). To add more AMBA 5 sidebands:

1. Add the new signal to `DeltaConfig` (e.g., a width field).
2. In `DeltaFlatCrossbar.__init__`, add the new port declarations when `amba5` is enabled.
3. Add routing logic in a new `generate_*_logic()` method.
4. Call the new method from `verilog()`.
5. If the new signal is covered by a check signal (a new payload field gets a `*CHK` per Table 5-1), add it to `_payload_chk_fields()`. That one list drives the ports, the carry mux, the ingress checkers and the error OR.
6. Update the DV suite (`dv/tests/test_delta_axis_flat_2x4_strb_amba5.py` and its harness) to exercise the new sideband.

## TWAKEUP design note

`TWAKEUP` is a hint, not a data beat. It is routed by `TDEST` without arbitration because it may precede `TVALID`. If a future sideband requires grant-based routing, follow the payload check-bit pattern in `generate_crossbar_mux()`.

## Check-signal design note

The payload check bits ride the same grant as `TDATA` and are carried, not regenerated, so a beat corrupted upstream still fails downstream. The crossbar also checks them on ingress (enabled by `TVALID`). It generates the single-bit checks for the signals it drives (`TVALIDCHK` and `TWAKEUPCHK` on slave ports, `TREADYCHK` on master ports) and checks the ones it receives. Every bit is one `rtl/common/dataint_parity` instance, odd parity, `CHUNKS=1`. A new check must follow the same rule: odd parity, one bit per 8 bits, top bit covers the remainder (IHI 0051B section 5.3).
