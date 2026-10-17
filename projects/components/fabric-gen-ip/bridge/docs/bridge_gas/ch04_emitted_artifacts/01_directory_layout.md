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

# Directory Layout

For each variant the generator creates a directory under the requested output dir:

```
rtl/generated/<bridge_name>/
├── <bridge_name>_pkg.sv
├── <bridge_name>.sv
├── <bridge_name>_xbar.sv
├── <master0>_adapter.sv
├── <master1>_adapter.sv
├── ...
├── <slave0>_adapter.sv
├── <slave1>_adapter.sv
├── ...
├── <bridge_name>.toml              (copied source config)
├── <bridge_name>_connectivity.csv  (copied connectivity matrix)
├── <bridge_name>_checkers.sv       (protocol-checker binds; simulation/formal only)
├── <bridge_name>_cfg_pkg.sv        (when use_cfg_regblock=true)
└── <bridge_name>_cfg.sv            (when use_cfg_regblock=true)

rtl/filelists/
├── <bridge_name>.f
└── <bridge_name>_checkers.f        (the bridge + checker + binds; never synthesis)
```

`<bridge_name>_checkers.sv` binds `formal/bridge/axi4_protocol_checker` to
every external AXI4/AXI5 port on that port's clock (GitHub #119 L3,
`CheckerBindGenerator`). Generated tests compile `<bridge_name>_checkers.f`
unless `BRIDGE_CHECKERS=0`.

If `--generate-tests` is used, the following are also written:

```
dv/tbclasses/
└── <tb_class_module>.py
dv/tests/
└── test_<bridge_name>.py
```

For `"mon"` variants the test runner is named `test_<bridge_name>_monitor.py`.

## Variant directories

The `"no"` variant writes to `<base_name>/`. The `"mon"` variant writes to `<base_name>_mon/`.

Example for a config with `name = "bridge_mix_e"` and `variants = ["no"]`:

```
rtl/generated/bridge_mix_e/
├── bridge_mix_e_pkg.sv
├── bridge_mix_e.sv
├── bridge_mix_e_xbar.sv
├── cpu_axi3_adapter.sv
├── dma_axi4_adapter.sv
├── host_apb_adapter.sv
├── ddr_axi3_adapter.sv
├── sram_axi4_adapter.sv
├── apb_periph_adapter.sv
├── subtractive_adapter.sv
├── bridge_mix_e.toml
└── bridge_mix_e_connectivity.csv
```
