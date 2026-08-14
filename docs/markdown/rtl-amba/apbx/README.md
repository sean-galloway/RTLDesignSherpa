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
| [apbx_xbar_thin.md](apbx_xbar_thin.md) | `apbx_xbar_thin` — the parameterized M×S combinational crossbar with weighted round-robin and runtime address decode |
| [apbx_xbar_variants.md](apbx_xbar_variants.md) | The generated fixed-configuration crossbars (`1to1`, `2to1`, `1to4`, `2to4`, `2to2_mixed`) built from APB boundary IP |

## Two families, one directory

They are genuinely different architectures and the choice matters:

| | `apbx_xbar_thin` | Generated variants |
|---|---|---|
| Topology | Any M×S, set by parameter | Fixed per generated file |
| Version selection | `MST_APB5` / `SLV_APB5` parameters | Baked in at generation time |
| Address map | Runtime inputs, per-slave base/limit/enable | Compile-time, uniform 64 KB regions |
| Protocol conversion | None — combinational passthrough | APB → cmd/rsp → APB |
| Added latency | Zero cycles | Multiple cycles |
| Best for | Sparse or reprogrammable maps, latency-critical paths | Timing closure at higher frequency |

The version story differs between them in a way worth stating plainly. The
thin core takes the versions as **parameters**, so one netlist covers every
combination and synthesis prunes what is unused. A generated variant instead
instantiates different boundary IP per port, so its versions are **structural**
and changing them means regenerating.

## Where the code lives

The RTL, generator, and testbenches are in the component area, not under
`rtl/amba/`:

```
projects/components/apbx-xbar/
├── bin/                    generator + convenience driver
│   ├── apbx_xbar_generator.py
│   └── generate_xbars.py
├── rtl/                    generator output (regenerate, do not hand-edit)
│   ├── apbx_xbar_thin.sv
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
