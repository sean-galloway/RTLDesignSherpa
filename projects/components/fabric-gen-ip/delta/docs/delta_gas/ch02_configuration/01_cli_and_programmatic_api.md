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

# CLI and Programmatic API

## `delta_generator.py` CLI

```bash
python3 delta_generator.py --masters 2 --slaves 4 --data-width 64 --output-dir ../rtl
```

| Flag | Default | Description |
|------|---------|-------------|
| `--topology` | `flat` | `flat` (implemented), `tree` (retired scaffolding), `both` (legacy alias; retired), or `mesh` (planned). |
| `--masters` | required | Number of master interfaces. |
| `--slaves` | required | Number of slave interfaces. |
| `--data-width` | 64 | `TDATA` width in bits. |
| `--user-width` | 1 | `TUSER` width. |
| `--strb-width` | 0 | `TSTRB` width; 0 omits `TSTRB` ports. |
| `--amba5` | False | Emit AMBA 5 `TWAKEUP`, the IHI 0051B ch. 5 odd-parity check signals and the per-port `*_parity_error` flags. Widths are fixed by the spec; requires a whole-byte `--data-width`. |
| `--output-dir` | `../rtl` | Destination directory. |
| `--nodes` | False | Also emit the `delta_split_1to2` primitive. |
| `--no-counters` | False | Disable the optional performance counters. |

: delta_generator.py CLI Flags

## `complete_tree_generator.py` CLI

| Flag | Description |
|------|-------------|
| `--type` | `merger`, `fanout`, or `fanin`. |
| `--size` | Number of inputs/outputs for fan-out/fan-in. |
| `--output` | Output directory (default `../rtl`). |

: complete_tree_generator.py CLI Flags

> **PLANNED** The mesh CLI below is the interface proposed by the [2026-10-13 mesh design spec](../../../../../../../docs/superpowers/specs/2026-10-13-delta-mesh-design.md). It is not implemented yet and is subject to change when implementation starts.
>
> ```bash
> delta_generator.py --topology mesh \
>   --cells-x 4 --cells-y 4 --cells-z K \
>   [--torus=x,y,z] [--source-route] [--speculation] \
>   [--data-width N] [--user-width N] [--amba5] [--no-counters] ...
> ```
>
> Mesh mode emits one cell module, `delta_mesh_cell`, and a fabric top that instantiates the `cells-x` × `cells-y` × `cells-z` grid. The hierarchy names (cell, tile, confluence, fabric) are for placement and documentation; the generator does not emit wrapper RTL for each level. The cell input buffers will expose a FIFO implementation knob (register file vs. SRAM).

## Programmatic API

The preferred programmatic entry point is the `DeltaConfig` dataclass plus `DeltaFlatCrossbar`:

```python
from delta_generator import DeltaConfig, DeltaFlatCrossbar

cfg = DeltaConfig(
    topology="flat",
    num_masters=2,
    num_slaves=4,
    data_width=64,
    dest_width=2,
    id_width=1,
    user_width=1,
    strb_width=8,
    amba5=True,
    registered_outputs=True,
    arbiter_type="round_robin",
    add_performance_counters=True,
)

gen = DeltaFlatCrossbar(cfg)
gen.verilog("../rtl")
```

`dest_width` and `id_width` are normally calculated from `num_slaves` and `num_masters` but may be overridden if the caller supplies them explicitly.
