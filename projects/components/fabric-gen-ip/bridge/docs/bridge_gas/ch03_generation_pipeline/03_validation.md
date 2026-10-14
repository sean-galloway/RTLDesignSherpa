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

# Validation

Validation runs immediately after loading. The function `validate_config(masters, slaves, connectivity)` in `bridge_pkg/config_validator.py` is the single gatekeeper.

## Validation order

1. **Per-port required fields** — `validate_required_fields(port)` for every master and slave.
2. **Channel and protocol values** — `validate_channels()` and `validate_protocol()`.
3. **Protocol constraints** — APB, WB4, AXI3, CDC.
4. **AXI5 feature validation** — `validate_axi5()`, wide-feature checks, poison connectivity, atomic read-return rules, axil5 feature checks.
5. **Slave ID width** — `validate_slave_id_widths()`.
6. **Address map** — `validate_address_map()`.
7. **Master-slave compatibility** — `validate_master_slave_compatibility()`.
8. **Dropped-sideband warnings** — `warn_axi5_dropped_sideband()` (non-fatal).

## Error behavior

Every validator raises `ValidationError(message)` on failure. `bridge_generator.py` catches the exception, prints the traceback, and returns `(False, [])` so the bulk driver can count the failure.

## Examples of validation failures

| Scenario | Validator | Message highlights |
|----------|-----------|--------------------|
| `channels = "rx"` | `validate_channels` | `Invalid channels 'rx'... Must be one of {'rw', 'rd', 'wr'}` |
| `protocol = "axi6"` | `validate_protocol` | `Invalid protocol 'axi6'... Must be one of {'axi3', 'axi4', 'axi5', 'apb', 'apb5', 'axil', 'axil5', 'wb4'}` |
| APB with `id_width = 4` | `validate_apb_constraints` | `must have id_width=0` |
| AXI5 `poison` on a path to an AXI4 slave | `validate_axi5_poison_connectivity` | `connected slave cannot carry it natively` |
| Overlapping slave windows | `validate_address_map` | `Address overlap detected` |
| `wr` master to `rd` slave | `validate_master_slave_compatibility` | `cannot connect to read-only slave` |

: Examples of validation failures

## Adding a new validation rule

To add a rule:

1. Write a validator function that accepts `(masters, slaves, connectivity)` or a single `PortSpec`.
2. Call it from `validate_config()` at the appropriate point in the order above.
3. Update this chapter and the configuration chapter with the new rule.

Keep validators stateless and raise `ValidationError` only; do not mutate the config.
