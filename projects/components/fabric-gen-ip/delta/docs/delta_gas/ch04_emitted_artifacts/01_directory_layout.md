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

# Directory Layout

```
delta/
├── bin/
│   ├── delta_generator.py            # framework-based flat crossbar generator
│   ├── complete_tree_generator.py    # tree primitive generator
│   ├── delta_generator_v1_backup.py  # legacy generator (reference only)
│   └── delta_performance_model.py    # performance estimation tool
├── rtl/
│   └── delta_axis_flat_<M>x<N>.sv    # generated flat crossbar
├── dv/
│   └── tests/                        # cocotb test suite
├── PRD.md                            # product requirements
└── CLAUDE.md                         # AI development guide
```

The generator writes directly into the directory specified by `--output-dir` (default `../rtl`). Unlike the APB crossbar, Delta does not currently maintain a batch script with a fixed variant table; callers generate the sizes they need.
