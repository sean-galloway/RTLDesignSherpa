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

# Adding a New Standard Variant

To add a new pre-generated fixture size:

1. Open `bin/generate_xbars.py`.
2. Add the `(masters, slaves)` tuple to the `variants` list for plain APB4, or add a `mixed` entry for a new version combination.
3. Add a matching cocotb test in `dv/tests/`.
4. Regenerate:

```bash
cd projects/components/fabric-gen-ip/apbx-xbar/bin
python generate_xbars.py
```

5. Run the DV suite:

```bash
cd ../dv/tests
make clean-all && make run-all-gate
```

6. Commit the generator change, the new RTL file, and the new test together.

## Naming convention

- Plain variants: `apbx_xbar_<M>to<N>.sv`
- Mixed-version variants: `apbx_xbar_<M>to<N>_<suffix>.sv`

The suffix must be alphanumeric with underscores and must be reflected in the `name_suffix` argument.
