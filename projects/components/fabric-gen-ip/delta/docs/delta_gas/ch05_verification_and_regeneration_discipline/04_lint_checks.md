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

# Lint Checks

The generated RTL must pass the project's lint flow.

## Common concerns

| Concern | Mitigation in generator |
|---------|-------------------------|
| Unpacked array lint | Arrays are declared as `logic [W-1:0] name [N]`; ensure the lint tool supports unpacked array ports. |
| Width mismatches | `DEST_WIDTH` and `ID_WIDTH` are computed from slave/master counts. |
| Latch inference | All `always_comb` blocks assign all outputs; no incomplete cases. |
| Uninitialized logic | Default assignments precede conditional overrides in every mux. |

: Lint Concerns and Mitigations

## Synthesis smoke test

Run a synthesis tool on the 2×4 variant after any generator change. The expected result is clean elaboration with no combinational loops and no latch inference.
