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

# When to Regenerate

Regenerate when any of the following change:

- `bin/apbx_xbar_generator.py`
- `bin/generate_xbars.py`
- The `apb4_slave` / `apb4_master` / `apb5_slave` / `apb5_master` boundary modules
- The `arbiter_round_robin` module

The standard regeneration workflow is:

```bash
cd projects/components/fabric-gen-ip/lattice-apbx-xbar/bin
python generate_xbars.py        # regenerates all standard variants into rtl/
```

After regeneration, run the DV suite:

```bash
cd ../dv/tests
make clean-all && make run-all-gate
```

## Pre-generated vs custom

Always check whether a pre-generated variant exists before generating a custom one. The pre-generated fixtures are the regression baseline; custom variants are for one-off sizes.
