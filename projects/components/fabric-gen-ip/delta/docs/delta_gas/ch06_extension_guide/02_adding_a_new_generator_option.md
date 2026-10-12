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

# Adding a New Generator Option

To add a scalar option:

1. Add the field to `DeltaConfig`.
2. Add the CLI argument to `main()` in `delta_generator.py`.
3. Pass the argument into `DeltaConfig(...)`.
4. Use the config field inside the appropriate `generate_*` method.
5. Document the option in this GAS, the HAS, and the PRD if it changes hardware behavior.
6. Add validation in `main()` or inside the generator method.
7. Add a DV test that exercises the new option.

## Backward compatibility

Default values must preserve existing generated output. If the new option changes the default port list, introduce it as an opt-in flag first.

## Example: adding a QoS sideband

```python
@dataclass
class DeltaConfig:
    ...
    qos_width: int = 0
```

Then emit `s_axis_tqos` / `m_axis_tqos` arrays and mux them in `generate_crossbar_mux()`.
