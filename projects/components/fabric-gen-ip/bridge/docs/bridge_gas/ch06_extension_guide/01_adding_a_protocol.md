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

# Adding a Protocol

Adding a new protocol to Bridge means adding a new value to the `protocol` enum, validating it, selecting the right converter/wrapper in the adapters, and updating the filelist logic.

## Step 1: Add the protocol to the validator

In `bridge_pkg/config_validator.py`:

1. Add the protocol string to `valid_protocols` in `validate_protocol()`.
2. Add a new `validate_<proto>_constraints()` function if the protocol has special rules (for example, allowed widths, channel restrictions, ID width rules).
3. Call the new validator from `validate_config()`.

## Step 2: Add converter/wrapper selection

In `bridge_pkg/generators/adapter_generator.py`:

- For a master protocol, decide which front-end converter module to instantiate.
- Add the protocol to the width-converter path selection.
- Emit the correct external port signals.

In `bridge_pkg/generators/slave_adapter_generator.py`:

- For a slave protocol, decide which completer shim to instantiate.
- Wire the internal AXI4 face to the shim.

## Step 3: Update the filelist

In `bridge_generator.py` `_emit_bridge_variant()`:

- Add `if any(m.protocol.lower() == '<proto>' for m in config.masters):` block to pull in the master-side converter closure.
- Add the corresponding slave-side block.

Always `-f` the converter's own closure filelist; do not hand-list individual `.sv` files.

## Step 4: Add a representative fixture

Add a TOML/CSV pair to `bin/test_configs/` and a line to `bridge_batch.csv` so the new protocol is exercised in regression.

## Step 5: Run the full regeneration and test

```bash
cd projects/components/fabric-gen-ip/bridge/bin
make clean && make all
python bridge_generator.py --bulk bridge_batch.csv --generate-tests
cd ../dv/tests
make clean-all && make run-<new_fixture>-func
```

## Example: how APB was added

APB master support uses `apb4_to_axi4` / `apb5_to_axi4` front-end converters. APB slave support uses `axi4_to_apb4_shim` / `axi4_to_apb5_shim`. The validator enforces `channels="rw"`, `data_width` in `{8,16,32}`, and `id_width=0`. The filelist pulls in the converter closures conditionally.
