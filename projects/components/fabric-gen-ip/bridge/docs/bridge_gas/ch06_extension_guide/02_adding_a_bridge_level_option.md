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

# Adding a Bridge-Level Option

Bridge-level options live in the `[bridge]` TOML table and become fields of `BridgeConfig`.

## Step 1: Add the dataclass field

In `bridge_pkg/config.py`, add a field to `BridgeConfig` with a sensible default:

```python
@dataclass
class BridgeConfig:
    ...
    my_option: bool = False
```

## Step 2: Add the TOML loader mapping

In `bridge_pkg/config_loader.py`, read the new key from the TOML tree and assign it to the `BridgeConfig` instance.

## Step 3: Validate if necessary

If the option has legal-value restrictions or conflicts with other options, add a validator in `bridge_pkg/config_validator.py` and call it from `validate_config()`.

## Step 4: Thread it into the emitter

In `bridge_generator.py` `_emit_bridge_variant()`, pass the option to `BridgeModuleGenerator`:

```python
gen = BridgeModuleGenerator(
    ...
    my_option=getattr(config, 'my_option', False),
)
```

## Step 5: Use the option in `BridgeModuleGenerator`

In `bridge_pkg/components/bridge_module_generator.py`:

1. Accept the option in `__init__`.
2. Store it as an instance attribute.
3. Use it to conditionally emit logic, instantiate modules, or modify the port list.

## Step 6: Document and test

- Add the key to this GAS chapter 2.
- Add a fixture to `bridge_batch.csv` that exercises the option.
- Regenerate and run the DV suite.

## Example: `xbar_pipeline`

`xbar_pipeline` is a bridge-level option that adds a registered skid stage inside the crossbar. It is loaded from TOML, stored in `BridgeConfig`, passed to `BridgeModuleGenerator`, and used by `CrossbarGenerator` to emit extra pipeline registers.
