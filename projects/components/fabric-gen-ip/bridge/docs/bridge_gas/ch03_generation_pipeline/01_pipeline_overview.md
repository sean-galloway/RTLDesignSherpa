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

# Pipeline Overview

The Bridge generation pipeline has five stages:

1. **Parse** — TOML and CSV files are read into Python data structures.
2. **Validate** — `validate_config()` checks semantic and protocol rules.
3. **Translate** — `PortSpec` objects are converted to `MasterConfig`/`SlaveInfo` objects consumed by the emitter.
4. **Emit RTL** — `BridgeModuleGenerator.generate_all()` writes package, adapters, crossbar, and top module.
5. **Emit collateral** — filelist, copied configs, optional regblock, optional tests.

Each variant (`no`, `mon`) runs stages 3–5 independently and writes to its own directory.

## Pipeline diagram

### Figure 3.1: Bridge Generator Pipeline

![Bridge generator pipeline](assets/graphviz/bridge_generator_pipeline.png)

Configuration enters at the top and passes down the center column: load, validate, then one pass per variant into the RTL emitter, which fans out to one sub-generator per file kind. Every output lands on the emitted-artifacts bar at the bottom. The dashed boxes run only when asked for: the cocotb test generator under `--generate-tests`, and the PeakRDL config regblock for a `use_cfg_regblock` bridge's `mon` variant. Nothing in the generator arbitrates, so the figure has no trapezium.

## Key files by stage

| Stage | File | Function |
|-------|------|----------|
| Parse | `bridge_pkg/config_loader.py` | `load_config()` reads TOML and CSV. |
| Validate | `bridge_pkg/config_validator.py` | `validate_config()` runs all checks. |
| Translate | `bridge_generator.py` | `_emit_bridge_variant()` builds `MasterConfig`/`SlaveInfo`. |
| Emit RTL | `bridge_pkg/components/bridge_module_generator.py` | `BridgeModuleGenerator.generate_all()` orchestrates sub-generators. |
| Emit adapters | `bridge_pkg/generators/adapter_generator.py` | `AdapterGenerator` emits master adapters. |
| Emit slave adapters | `bridge_pkg/generators/slave_adapter_generator.py` | `SlaveAdapterGenerator` emits slave adapters. |
| Emit crossbar | `bridge_pkg/generators/crossbar_generator.py` | `CrossbarGenerator` emits the internal crossbar. |
| Emit package | `bridge_pkg/generators/package_generator.py` | `PackageGenerator` emits the SV package. |
| Emit filelist | `bridge_generator.py` | `_emit_bridge_variant()` writes the `.f` filelist. |
| Emit tests | `bridge_generator.py` | `generate_tests()` / `generate_monitor_tests()` write cocotb files. |
| Emit cfg | `bridge_pkg/generators/cfg_rdl_generator.py` | `CfgRdlGenerator` emits the PeakRDL register block. |
