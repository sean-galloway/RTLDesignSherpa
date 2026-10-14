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

Any change to the files listed below must be followed by a full regeneration of every standard variant and a full regression run.

| Source | Why it forces regeneration |
|--------|---------------------------|
| `bin/apbx_xbar_generator.py` | Every emitted line comes from this file. |
| `bin/generate_xbars.py` | Drives the variant table and default parameters. |
| `rtl/common/apb4_slave.sv` / `apb5_slave.sv` | Boundary module behavior changes propagate into every master-side instance. |
| `rtl/common/apb4_master.sv` / `apb5_master.sv` | Same for slave-side instances. |
| `rtl/common/arbiter_round_robin.sv` | Arbitration timing or fairness changes affect every multi-master variant. |

: Sources Requiring Full Regeneration

## Regeneration command

```bash
cd projects/components/fabric-gen-ip/lattice-apbx-xbar/bin
python generate_xbars.py
```

After regeneration, the only expected `git diff` should be in `rtl/*.sv` and, if the RLB variant was affected, `retro_legacy_blocks/rtl/apbx_xbar/apbx_xbar_1to10.sv`.

## Do not hand-edit generated files

The `.sv` files in `rtl/` are generator output. Hand-edits will be overwritten on the next regeneration and are not reviewable as source changes. Fix the generator instead.
