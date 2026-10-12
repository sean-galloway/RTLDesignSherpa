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

# Generator Entry Points

## Low-level generator

```bash
python3 apbx_xbar_generator.py --masters 2 --slaves 4 --output apbx_xbar_2to4.sv
```

CLI flags are documented in the configuration chapter.

## Convenience batch script

```bash
python3 generate_xbars.py              # all standard variants
python3 generate_xbars.py --masters 3 --slaves 6
python3 generate_xbars.py --masters 4 --slaves 8 --base-addr 0x80000000
```

## Programmatic API

```python
from apbx_xbar_generator import generate_apbx_xbar

code = generate_apbx_xbar(
    num_masters=2,
    num_slaves=4,
    base_addr=0x10000000,
    addr_width=32,
    data_width=32,
    output_file="apbx_xbar_2to4.sv",
    slave_size=0x10000,
    master_versions=['apb4', 'apb4'],
    slave_versions=['apb4', 'apb4'],
    name_suffix="",
    enable_parity=False,
)
```

The function returns the generated SystemVerilog as a string and also writes the file when `output_file` is provided.
