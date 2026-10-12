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

Regenerate the Delta fixtures when any of the following change:

- `bin/delta_generator.py`
- `bin/complete_tree_generator.py`
- `bin/rtl_generators/verilog/module.py` (the framework base class)
- The area regression flow or lint rules

## Standard regeneration workflow

```bash
cd projects/components/fabric-gen-ip/delta/bin
python delta_generator.py --masters 2 --slaves 4 --output-dir ../rtl
python complete_tree_generator.py --type merger --output ../rtl
```

After regeneration, run the DV suite:

```bash
cd ../dv/tests
make clean-all && make run-all-gate
```

## Pre-generated vs custom

Always check whether a pre-generated fixture exists before generating a custom one. The pre-generated fixtures are the regression baseline; custom variants are for one-off sizes.
