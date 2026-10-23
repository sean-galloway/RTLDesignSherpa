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

# Configuration Loading

Configuration loading is implemented in `bridge_pkg/config_loader.py`. The entry point is `load_config(ports_file, connectivity_file=None)`.

## TOML parsing

The loader uses Python's `tomllib` (or `tomli` on older Pythons) to read the TOML file. It expects:

- A `[bridge]` table with scalar keys and `[[bridge.masters]]` / `[[bridge.slaves]]` arrays.
- An optional `[bridge.mon_group]` table.
- An optional `[bridge.defaults]` table with a `skid_depths` sub-table.

Hex strings such as `"0x10000000"` are accepted for `base_addr` and `addr_range`.

## Connectivity CSV

The connectivity matrix is a CSV with the first column labeled `master\slave` and subsequent columns named after slaves. Example:

```csv
master\slave,ddr,sram,apb_periph
cpu,1,1,0
dma,1,0,1
```

If `connectivity_file` is `None`, `find_connectivity_csv(ports_file)` searches for `<stem>_connectivity.csv` next to the TOML file.

The loader builds a dictionary `connectivity[master_name] = set(slave_names)`.

## `BridgeConfig` construction

`load_config()` returns a `BridgeConfig` dataclass (`bridge_pkg/config.py`) populated with:

- `masters`: list of `PortSpec` (direction="master")
- `slaves`: list of `PortSpec` (direction="slave")
- `connectivity`: dict mapping master names to sets of slave names
- bridge-level fields such as `variants`, `xbar_pipeline`, `arbitration`, `mon_preset`, `use_cfg_regblock`, `mon_group`
- per-port defaults resolved from `[bridge]` into each `PortSpec`: `max_outstanding` (power of two 2..64) and, on masters, `rate_buffer` (0 or 2..256 wide beats; the generator uses it only on upsized paths into shared slaves) and `id_remap`
- a `[bridge].preset` (`_PRESETS`; only `"xbar"` today) changes the defaults those resolve from -- `latency`, `rate_buffer`, `id_remap` -- before any port is read; an explicit key still wins

The subtractive catch-all slave is **not** added by the loader; `BridgeModuleGenerator` appends it internally during emission.

## Normalization

- Port prefixes are **not** normalized by the loader; normalization happens later in `bridge_generator.py` via `_normalize_prefix()`.
- `MonGroupConfig` normalizes the deprecated `"axil"` spelling to `"axil4"` in `__post_init__`.
- `dest_width` and `id_width` are not relevant to Bridge; those are Delta-specific.
