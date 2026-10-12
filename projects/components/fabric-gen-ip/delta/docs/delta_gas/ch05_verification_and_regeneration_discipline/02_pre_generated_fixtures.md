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

# Pre-Generated Fixtures

Delta does not currently ship a fixed family of pre-generated sizes. The recommended baseline fixtures are generated on demand with:

```bash
python delta_generator.py --masters 2 --slaves 4 --data-width 64 --output-dir ../rtl
python delta_generator.py --masters 4 --slaves 4 --data-width 64 --output-dir ../rtl
python delta_generator.py --masters 2 --slaves 4 --data-width 64 --amba5 --output-dir ../rtl
```

If the project later adopts a canonical fixture set, add a `generate_all.py` batch script and document the fixed sizes here.

## Custom variants

Custom sizes are fully supported. When generating a custom variant, record the exact command in the subsystem integration notes so the fixture can be reproduced.
