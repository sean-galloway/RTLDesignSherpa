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

# CLI and Programmatic API

The generator is invoked either directly for a custom crossbar or through the batch script for the standard family.

## `apbx_xbar_generator.py`

```bash
python3 apbx_xbar_generator.py --masters 2 --slaves 4 --output apbx_xbar_2to4.sv
```

| Flag | Short | Default | Description |
|------|-------|---------|-------------|
| `--masters` | `-m` | required | Number of master interfaces (1-16). |
| `--slaves` | `-s` | required | Number of slave interfaces (1-16). |
| `--base-addr` | `-b` | `0x10000000` | Base address of the slave address map. |
| `--slave-size` | | `0x1000` | Address space per slave; must be a power of two and at least 256 bytes. |
| `--addr-width` | `-a` | 32 | APB PADDR width. |
| `--data-width` | `-d` | 32 | APB PWDATA/PRDATA width. |
| `--output` | `-o` | `apbx_xbar_<M>to<N>.sv` | Output filename. |

: Core Generator CLI Options

The CLI does **not** expose per-port APB5 or parity knobs; those are controlled by the programmatic API and the batch script.

## `generate_xbars.py`

```bash
python3 generate_xbars.py              # regenerate all standard variants
python3 generate_xbars.py --masters 3 --slaves 6
python3 generate_xbars.py --masters 4 --slaves 8 --base-addr 0x80000000 --slave-size 0x10000
```

| Flag | Short | Default | Description |
|------|-------|---------|-------------|
| `--masters` | `-m` | (all) | Masters for a custom variant. |
| `--slaves` | `-s` | (all) | Slaves for a custom variant. |
| `--base-addr` | `-b` | `0x10000000` | Base address for custom variant. |
| `--slave-size` | | `0x10000` | Stride for custom variant (default matches the shipped family). |

: Batch Generator CLI Options

The batch script explicitly passes `slave_size=0x10000` to the generator so the shipped family uses 64KB windows. Omitting the flag would silently fall back to the generator's 4KB default, which is why the batch script always passes it.

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

The function returns the generated module as a string and writes the file when `output_file` is provided. The `master_versions` and `slave_versions` lists are the only way to request APB5 ports or the mixed 2×2 variant; the CLI is kept narrow because mixed-version generation is normally driven by `generate_xbars.py`.
