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

# Full Regeneration Rule

Any change to the files listed below must be followed by regeneration of the affected fixtures and a full regression run.

| Source | Why it forces regeneration |
|--------|---------------------------|
| `bin/delta_generator.py` | All flat crossbar output comes from this file. |
| `bin/complete_tree_generator.py` | All tree primitive output comes from this file. |
| `bin/rtl_generators/verilog/module.py` | Framework changes affect header/footer formatting. |

: Sources That Force Regeneration

## Regeneration command

```bash
cd projects/components/fabric-gen-ip/delta/bin
python delta_generator.py --masters 2 --slaves 4 --output-dir ../rtl
python complete_tree_generator.py --type merger --output ../rtl
```

After regeneration, the only expected `git diff` should be in `rtl/`.

## Do not hand-edit generated files

The `.sv` files in `rtl/` are generator output. Hand-edits will be overwritten on the next regeneration. Fix the generator instead.
