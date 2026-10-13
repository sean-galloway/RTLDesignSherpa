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

# Adding a New Generator Option

To add a scalar option that affects all variants (for example, a new default `slave_size`):

1. Add the argument to `apbx_xbar_generator.py`'s `argparse` block and pass it through `generate_apbx_xbar`.
2. Add the same argument to `generate_xbars.py` if users should be able to override it for the standard family.
3. Document the option in this GAS, the HAS, and the PRD if it changes the hardware behavior.
4. Add validation near the top of `generate_apbx_xbar`.
5. Regenerate and run the full DV suite.

## Backward compatibility

Default values must preserve existing generated output. If the new option changes the default address map or port list, introduce it as an opt-in flag first and migrate the standard variants in a separate commit.
