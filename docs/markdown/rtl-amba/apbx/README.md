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

# APBX Crossbar

The APB crossbar family. It sits in its own directory rather than under
`apb4/` or `apb5/` because it is not tied to either: every port carries an
independent version, so one fabric can be all-APB4, all-APB5, or a mix.

| Page | Covers |
|------|--------|
| [apbx_xbar_variants.md](apbx_xbar_variants.md) | The generated fixed-configuration crossbars (`1to1`, `2to1`, `1to4`, `2to4`, `2to2_mixed`) built from APB boundary IP |

## One architecture

Every crossbar here is generator output with the same shape: APB → cmd/rsp
→ APB across registered skid buffers, with the topology, per-slave window
size and per-port APB version all **baked in at generation time**. Changing
any of them means regenerating, not re-elaborating — the boundary IP
instantiated on each port differs, so the version choice is structural
rather than a parameter mask.

A second family once lived here: `apbx_xbar_thin`, a hand-written
combinational M×S core with weighted round-robin and runtime-programmable
windows. It was retired and deleted on 2026-08-27.

## Where the code lives

The RTL, generator, and testbenches are in the component area, not under
`rtl/amba/`:

```
projects/components/apbx-xbar/
├── bin/                    generator + convenience driver
│   ├── apbx_xbar_generator.py
│   └── generate_xbars.py
├── rtl/                    generator output (regenerate, do not hand-edit)
│   ├── apbx_xbar_{1to1,2to1,1to4,2to4,2to2_mixed}.sv
│   ├── filelists/
│   └── wrappers/           hand-written testbench scaffolding
└── dv/tests/               CocoTB testbenches
```

Formal proofs are separate again, under `formal/apbx_xbar/`.

## Related

- [../apb4/README.md](../apb4/README.md) — the APB4 primitives an all-APB4 build is made of
- [../apb5/README.md](../apb5/README.md) — the APB5 primitives used on APB5 ports

## Navigation

- **[← Back to rtl-amba Index](../index.md)**
- **[← Back to Main Documentation Index](../../index.md)**
