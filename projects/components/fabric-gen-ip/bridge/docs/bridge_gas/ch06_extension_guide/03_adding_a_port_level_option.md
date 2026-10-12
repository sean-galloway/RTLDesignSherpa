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

# Adding a Port-Level Option

Port-level options are fields of `PortSpec`. They affect one port at a time.

## Step 1: Add the `PortSpec` field

In `bridge_pkg/config.py`, add a field to `PortSpec` with a default:

```python
@dataclass
class PortSpec:
    ...
    my_port_option: bool = False
```

## Step 2: Load it from TOML

In `bridge_pkg/config_loader.py`, copy the TOML key into the `PortSpec` constructor for both masters and slaves.

## Step 3: Validate it

If the option has constraints, add a validator in `bridge_pkg/config_validator.py`. For example, `cdc` is validated by `validate_cdc_constraints()` to ensure it is only used on AXI4 slave ports.

## Step 4: Thread it into `MasterConfig` / `SlaveInfo`

In `bridge_generator.py` `_emit_bridge_variant()`, pass the option through when building `MasterConfig` or `SlaveInfo`:

```python
master_config = MasterConfig(
    ...
    my_port_option=getattr(master_spec, 'my_port_option', False),
)
```

## Step 5: Use it in the adapter generator

In `bridge_pkg/generators/adapter_generator.py` or `slave_adapter_generator.py`, read the option from the config struct and emit conditional logic.

## Step 6: Update the filelist if needed

If the option requires additional IP, add conditional filelist lines in `bridge_generator.py`.

## Example: `cdc`

The `cdc` port option is a `PortSpec` field. It is validated as AXI4-slave-only, passed through `SlaveInfo`, and used by `SlaveAdapterGenerator` to insert `axi4_cdc_{wr,rd}`. The filelist conditionally pulls in `axi4_cdc_wr.f` and `axi4_cdc_rd.f`.
