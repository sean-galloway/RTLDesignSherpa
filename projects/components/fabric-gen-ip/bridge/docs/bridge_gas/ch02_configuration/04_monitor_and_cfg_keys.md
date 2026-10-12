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

# Monitor and CFG Subsystem Keys

Bridge can optionally emit a monitor infrastructure and a cfg register block. This section documents the keys that control those subsystems.

## Monitor subsystem

The `"mon"` variant wraps each enabled port with a `_monlite` timing wrapper. The wrapper exposes a `monbus_*` packet interface that feeds a per-bridge `monbus_arbiter` and, by default, a `monbus_axil4_axil4_group`.

### Bridge-level monitor keys

| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `mon_preset` | string | `"lite"` | Baseline reporter enables. Since 2026-09-26 all monitored ports use `axi_monitor_lite`, so every preset resolves to the same hardware; the field is kept for backward-compatible config loading. |
| `use_all_monitors` | boolean | `false` | Override every port's `use_monitor` to `true`. |
| `use_no_monitors` | boolean | `false` | Override every port's `use_monitor` to `false`. Mutually exclusive with `use_all_monitors`. |

### Per-port monitor keys

| Key | Type | Default | Description |
|-----|------|---------|-------------|
| `use_monitor` | boolean | `true` | Include the `_monlite` wrapper on this port in a `"mon"` variant. |
| `mon_add` | list | `[]` | Extra reporter cones to enable beyond the preset. |
| `mon_remove` | list | `[]` | Reporter cones to disable from the preset. |

`MON_CONES` in `bridge_pkg/config.py` defines the valid cone names: `error`, `timeout`, `compl`, `threshold`, `perf`, `debug`.

### `[bridge.mon_group]` table

This table selects the internal monbus aggregation module. See "Bridge-Level TOML Keys" for the full schema. The selected module is:

```python
f"monbus_{slave_protocol}_{master_protocol}_group"
```

Examples: `monbus_axil4_axil4_group`, `monbus_axi4_axi4_group`.

When `internal_axil_group = false`, the bridge still instantiates the `monbus_arbiter` but exposes its aggregated stream as `monbus_agg_*` top-level outputs, letting an external consumer provide the AXIL group.

## CFG register block

Setting `use_cfg_regblock = true` replaces the 350+ individual `cfg_<port>_<idx>_<chan>_*` top-level pins with a PeakRDL-generated register block.

### What changes

- `CfgRdlGenerator` (`bridge_pkg/generators/cfg_rdl_generator.py`) builds an RDL schema from the adapter list and `BridgeModuleGenerator._MON_GROUP_CFG`.
- PeakRDL emits `<bridge_name>_cfg_pkg.sv` and `<bridge_name>_cfg.sv` into the bridge directory.
- `bridge_generator.py` patches the top module to narrow the 32-bit `s_cfg_axil_*addr` into the regblock's actual address width.
- The filelist gains the cfg package and body, plus a Verilator waiver for PeakRDL's `field_combo` `MULTIDRIVEN` warning.

### Per-port cfg fields

`CfgAdapterPort` is constructed in `bridge_generator.py` for every master and every non-internal slave. Fields include:

| Field | Meaning |
|-------|---------|
| `name` | Port name |
| `idx` | Index within direction |
| `has_wr` / `has_rd` | Which directions exist after channel trimming |
| `perfmon_enabled` | Whether perf counters exist for this port |
| `n_addr_ranges` | Number of address ranges (currently 0) |
| `addr_width` | Address width for this adapter |

The subtractive catch-all slave is deliberately excluded from the cfg map so that adding or removing it does not shift register offsets.
