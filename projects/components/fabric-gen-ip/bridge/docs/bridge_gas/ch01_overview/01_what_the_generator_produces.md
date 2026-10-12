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
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# What the Generator Produces

The Bridge generator (`bin/bridge_generator.py`) emits a complete, synthesizable AXI4/AXI5 crossbar from a TOML port description and a CSV connectivity matrix. The output is **not** a parameterized Verilog template: every width, count, and protocol conversion is resolved at generation time, and the top module exposes no parameters.

## Generated Artifact Family

For each requested variant (`no` or `mon`), the generator writes a directory under `rtl/generated/<bridge_name>/` containing:

| File | Stamped generator |
|------|-------------------|
| `<bridge_name>_pkg.sv` | `PackageGenerator` |
| `<bridge_name>.sv` | `BridgeModuleGenerator` |
| `<bridge_name>_xbar.sv` | `CrossbarGenerator` |
| `<master>_adapter.sv` | `AdapterGenerator` (per master) |
| `<slave>_adapter.sv` | `SlaveAdapterGenerator` (per slave) |
| `<bridge_name>.f` | `bridge_generator.py` (filelist) |
| `<bridge_name>.toml` | copied source config |
| `<bridge_name>_connectivity.csv` | copied connectivity matrix |
| `__cfg_*_pkg.sv` / `<bridge_name>_cfg.sv` | `CfgRdlGenerator` (only when `use_cfg_regblock = true`) |

The header comment in each `.sv` file names the generator class that produced it. This is the fastest way to tell whether a file is generated and which part of the pipeline owns it.

## What Each Variant Means

The TOML `[bridge].variants` list selects which variants to emit:

- `"no"` — bare bridge, no monitor wrapper instances.
- `"mon"` — bridge with `_monlite` wrappers on every enabled port, plus the monbus arbiter and an internal AXIL4/AXIL4 group (unless `internal_axil_group = false`).

Both variants are fully independent; each gets its own directory and its own filelist.

## Scope of Generation

The generator resolves:

- Port prefixes, channel subsets (`rw`/`wr`/`rd`), widths, and protocol variants.
- Width converters (`axi4_dwidth_converter_{wr,rd}`) inserted only where master and slave data widths differ.
- Protocol shims (`axi4_to_apb4_shim`, `axi4_to_apb5_shim`, `axi4_to_axil4_*`, `axi4_to_axil5_*`, `axi4_to_axi3`, `axi4_to_wb4`, AXI5 boundary wrappers) selected by the port `protocol` field.
- The subtractive catch-all slave (`axi4_subtractive_slave`), always present and wired to unmapped addresses.
- Optional monitor wrappers and a cfg register block.

The generator does **not** emit testbench code unless `--generate-tests` is passed.
