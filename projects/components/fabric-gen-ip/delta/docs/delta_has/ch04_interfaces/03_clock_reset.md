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

# Clock and Reset

## Clock

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `aclk` | 1 | Input | Positive-edge clock for all registered state. |

: Clock Signal

All registered logic (grants, `last_grant`, packet-active flags, counters) is clocked on the rising edge of `aclk`. Combinational decode and mux logic is not registered.

## Reset

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| `aresetn` | 1 | Input | Active-low asynchronous reset. |

: Reset Signal

`aresetn` resets all registered state:

- `grant_matrix` to zero.
- `last_grant` to zero.
- `packet_active` to zero.
- Packet counters to zero.

The reset assertion is asynchronous; de-assertion is synchronous to `aclk` in the checked-in RTL through the `ALWAYS_FF_RST` macro.

## Clocking Rules

- All masters and slaves share the same `aclk`.
- Delta does not contain clock-domain crossing logic.
- Inputs are sampled on the rising edge of `aclk`; outputs are driven combinationally or from registers.

## Reset Recommendations

- Assert `aresetn` for at least several clock cycles after power and clock stability.
- Do not rely on Delta's outputs during reset; combinational mux outputs may be zero or undefined during reset.
