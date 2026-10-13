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

# Adding APB5 Parity or Sideband

The APB5 sideband and parity machinery is already present in the generator. Extending it usually means widening a sideband signal or changing how parity is computed.

## Widening sideband signals

The generator hard-codes 1-bit user signals (`AUSER_WIDTH=1`, `WUSER_WIDTH=1`, etc.). To support wider user fields:

1. Add a new generator option (e.g., `user_width`).
2. Pass the width through to the `apb5_slave`/`apb5_master` parameterization.
3. Update the fabric cmd/rsp declarations to carry the wider fields.
4. Update the port list generation to declare the wider APB5 pins.

## Changing parity behavior

The check signals are the AMBA APB (IHI 0024E) chapter 5 `*CHK` set. They use odd parity, with one bit per 8 bits of the covered signal. The boundary modules check them on entry and generate them on exit, and the crossbar only routes them. The one exception is a completer port's `PWAKEUPCHK`, which the crossbar computes as `~PWAKEUP` over its own wake OR (see *Mixed APB4/APB5 and Parity*). To change parity width or algorithm:

1. Modify `apb5_slave` and `apb5_master` to support the new scheme.
2. Update the crossbar generator's parity vector widths and tie-offs accordingly.
3. Extend `dv/tests/test_apbx_xbar_parity.py`, which generates a parity-enabled variant, checks every check output for odd parity, and injects check-bit errors against the `parity_error_*` outputs.

Remember that parity is checked and regenerated at each boundary. It never crosses the cmd/rsp fabric.
