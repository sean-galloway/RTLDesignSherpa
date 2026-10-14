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

# Pre-Generated Fixtures

The component ships with five pre-generated fixtures:

| File | Masters | Slaves | Notes |
|------|---------|--------|-------|
| `apbx_xbar_1to1.sv` | 1 | 1 | Simple passthrough; no arbiter. |
| `apbx_xbar_2to1.sv` | 2 | 1 | Arbitration only, no address decode. |
| `apbx_xbar_1to4.sv` | 1 | 4 | Address decode only, no arbitration. |
| `apbx_xbar_2to4.sv` | 2 | 4 | Full crossbar: decode + arbitration. |
| `apbx_xbar_2to2_mixed.sv` | 2 | 2 | APB4/APB5 mixed-port boundary test. |

: Pre-Generated Fixtures

These fixtures are the regression baseline. They are generated with:

- `base_addr = 0x10000000`
- `slave_size = 0x10000` (64KB windows)
- `addr_width = 32`, `data_width = 32`

The mixed variant uses `master_versions=['apb4','apb5']` and `slave_versions=['apb5','apb4']`.

## When to add a new fixture

Add a new standard fixture only when:

1. A new size is required by multiple subsystems, or
2. A new port-version combination needs continuous regression coverage.

Add the new entry to the `variants` or `mixed` table in `generate_xbars.py`, regenerate, and add a matching cocotb test.
