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

# Generator Entry Points

## Flat crossbar generator

```bash
python3 delta_generator.py --masters 2 --slaves 4 --data-width 64 --output-dir ../rtl
```

CLI flags are documented in the configuration chapter.

## Tree primitives generator

```bash
python3 complete_tree_generator.py --type merger --output ../rtl
python3 complete_tree_generator.py --type fanout --size 4 --output ../rtl
python3 complete_tree_generator.py --type fanin --size 4 --output ../rtl
```

## Programmatic API

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
    strb_width=0,
    amba5=False,
    registered_outputs=True,
    arbiter_type="round_robin",
    add_performance_counters=True,
)
gen = DeltaFlatCrossbar(cfg)
gen.verilog("../rtl")
```

The `verilog()` method writes `delta_axis_flat_<M>x<N>.sv` into the requested directory using the `Module` framework's `write()` helper.
