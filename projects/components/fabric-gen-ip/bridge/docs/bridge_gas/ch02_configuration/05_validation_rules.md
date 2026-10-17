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

# Validation Rules

Configuration validation is centralized in `bridge_pkg/config_validator.py`. The loader calls `validate_config(masters, slaves, connectivity)` before any RTL is emitted. Validation failures raise `ValidationError` and stop generation.

## Field validation (`validate_required_fields`)

- Every port must have `name` and `prefix`.
- `data_width` and `addr_width` must be positive.
- `axi4` masters must have `id_width > 0`.
- `axil`/`axil5` masters must have `id_width == 0`.
- `apb`/`apb5`/`wb4`/`axi3` masters must have `addr_width == 32`.
- Slaves must have `base_addr` and a positive `addr_range`.
- Slave `base_addr` and `addr_range` must be 4 KiB-aligned / a multiple of 4 KiB.

## Channel and protocol validation

- `channels` must be one of `rw`, `wr`, `rd` (`validate_channels`).
- `protocol` must be one of `axi3`, `axi4`, `axi5`, `apb`, `apb5`, `axil`, `axil5`, `wb4` (`validate_protocol`).
- Slaves must explicitly specify `channels` (`validate_slave_channels_explicit`).

## Protocol-specific constraints

### APB / APB5 (`validate_apb_constraints`)

- `channels` must be `rw`.
- `data_width` must be 8, 16, or 32.
- `id_width` must be 0.

### Wishbone B4 (`validate_wb4_constraints`)

- `channels` must be `rw`.
- `data_width` must be 8, 16, 32, or 64.
- `id_width` must be 0.

### AXI3 (`validate_axi3`)

- AXI3 masters must have `id_width > 0`.
- `data_width` must be 32, 64, 128, or 256.
- CDC is not supported.

### AXI5 (`validate_axi5`)

- `axi5_features` may appear only on `axi5` or `axil5` ports.
- Droppable features: `nsaid`, `trace`, `mpam`, `mecid`, `unique`, `chunking`.
- Connectivity-gated features: `poison`, `atomic`, `mte`.
- `mte` and `chunking` require `data_width >= 128` (`validate_axi5_wide_features`).
- `poison`, `atomic`, `mte` require every connected path to be native AXI5 with the feature enabled and the same data width (`validate_axi5_poison_connectivity`).
- An `rw` AXI5 master with `atomic` may only connect to `rw` AXI5 slaves (`validate_axi5_atomic_read_return`).
- `axil5` ports accept only `user` and `exclusive` as forwardable features (`validate_axil5_features`).

## Master-slave compatibility (`validate_master_slave_compatibility`)

- A `wr` master cannot connect to a `rd` slave.
- A `rd` master cannot connect to a `wr` slave.
- Compatibility is checked only for connected pairs (per the CSV connectivity matrix).

## Address map validation (`validate_address_map`)

- Positively-decoded slave windows must not overlap.
- The subtractive catch-all (`internal=true`) is excluded from overlap checks.

## Slave ID width (`validate_slave_id_widths`)

With more than one master, every AXI slave port's ID is widened by `$clog2(NUM_MASTERS)` master-index bits. The validator checks that each slave's declared `id_width` is at least:

```python
widest_master_id_width + clog2(num_masters)
```

## CDC constraints (`validate_cdc_constraints`)

- `cdc=true` is legal only on AXI4 ports, master (GitHub #119 L2) or external slave.
- Internal slaves cannot be CDC ports.

## Warning for dropped sideband (`warn_axi5_dropped_sideband`)

Droppable AXI5 sideband that terminates mid-path prints a generation-time warning naming the path and the reason (non-AXI5 peer, missing feature, or width converter).
