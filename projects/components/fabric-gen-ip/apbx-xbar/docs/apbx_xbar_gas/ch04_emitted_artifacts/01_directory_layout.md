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

The generator writes a single `.sv` file per invocation. The standard family is organized as follows:

```
apbx-xbar/
├── bin/
│   ├── apbx_xbar_generator.py      # low-level generator
│   └── generate_xbars.py           # batch generator
├── rtl/
│   ├── apbx_xbar_1to1.sv
│   ├── apbx_xbar_2to1.sv
│   ├── apbx_xbar_1to4.sv
│   ├── apbx_xbar_2to4.sv
│   └── apbx_xbar_2to2_mixed.sv
└── dv/
    └── tests/                      # cocotb test suite
```

The Retro Legacy Blocks 1-to-10 variant is emitted outside this tree because it is consumed by another component:

```
retro_legacy_blocks/rtl/apbx_xbar/apbx_xbar_1to10.sv
```

This external placement is intentional; it prevents the RLB crossbar from drifting away from the family fixes.
