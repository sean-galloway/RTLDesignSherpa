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

# Adapter and Crossbar Emission

After validation, `bridge_generator.py` calls `_emit_bridge_variant()` for each variant in `BridgeConfig.variants`. That function translates `PortSpec` objects into `MasterConfig`/`SlaveInfo` objects and drives `BridgeModuleGenerator`.

## Translation to emitter structs

`MasterConfig` and `SlaveInfo` are lightweight structs consumed by the generators. Key fields:

| Field | `MasterConfig` | `SlaveInfo` |
|-------|----------------|-------------|
| `name` | port name | port name |
| `prefix` | normalized prefix | normalized prefix |
| `data_width` | int | int |
| `addr_width` | int | int |
| `id_width` | int | int |
| `channels` | `rw`/`wr`/`rd` | `rw`/`wr`/`rd` |
| `slave_connections` | list of slave indices | — |
| `protocol` | string | string |
| `use_monitor` | bool | bool |
| `mon_enables` | dict | dict |
| `axi5_features` | list | list |
| `cdc` | bool | bool |
| `enable_ooo` | — | bool |
| `internal` | — | bool |

: Translation to emitter structs

## `BridgeModuleGenerator` construction

`_emit_bridge_variant()` instantiates `BridgeModuleGenerator` with:

```python
BridgeModuleGenerator(
    bridge_name=output_name,
    enable_monitoring=use_monitor,
    internal_axil_group=internal_axil_group,
    use_all_monitors=...,
    use_no_monitors=...,
    use_cfg_regblock=...,
    mon_group=...,
    xbar_pipeline=...,
    arbitration=...,
    qos_aging_shift=...,
    id_track_bits=...,
)
```

Then it calls `gen.add_master(master)` and `gen.add_slave(slave)` for every port, and finally `gen.generate_all(bridge_dir)`.

## Sub-generators

`BridgeModuleGenerator.generate_all()` returns a dict mapping a tag to a file path. The tags are:

| Tag | Generator class | Output file |
|-----|-----------------|-------------|
| `package` | `PackageGenerator` | `<bridge>_pkg.sv` |
| `adapter_<name>` | `AdapterGenerator` | `<name>_adapter.sv` |
| `slave_adapter_<name>` | `SlaveAdapterGenerator` | `<name>_adapter.sv` |
| `bridge` | `BridgeModuleGenerator` itself | `<bridge>.sv` |
| `crossbar` | `CrossbarGenerator` | `<bridge>_xbar.sv` |

: Sub-generators

The package is always emitted first so later modules can `import` it. Adapter file names are based on the port `name`, not the prefix.

## Master adapter (`AdapterGenerator`)

The master adapter:

1. Declares the external port with the configured prefix and channel subset.
2. Optionally instantiates a timing wrapper (`axi4_slave_wr/rd`, `_monlite` variants, or AXI5 boundary wrappers).
3. Optionally instantiates a protocol converter (`apb4_to_axi4`, `axi3_to_axi4`, `wb4_to_axi4`, `axi5_atomic_filter`, etc.).
4. Generates per-width output paths (32b, 64b, 128b, 256b, 512b) and inserts `axi4_dwidth_converter_{wr,rd}` or `axil_to_axi4_wide_align_{wr,rd}` only where needed.
5. Emits address decode logic producing `<name>_slave_select_aw` / `ar` and a `bridge_id` sideband.

## Slave adapter (`SlaveAdapterGenerator`)

The slave adapter:

1. Declares the external slave port with the configured prefix and protocol.
2. Optionally instantiates a timing wrapper or protocol shim (`axi4_to_apb4_shim`, `axi4_to_axi3`, `axi4_to_wb4`, AXI5 boundary wrappers).
3. Carries the response tracker: by ID (master index from the returned ID's prefix bits, an outstanding counter to `max_outstanding`) for an AXI3/AXI4/AXI5 slave of a multi-master bridge or an `enable_ooo` slave (`SlaveAdapterGenerator.track_by_id`), an in-order `bridge_id` FIFO otherwise. An AXI3 slave takes the AXI4 path throughout (timing wrapper, tracker, request slots), and `axi4_to_axi3` is emitted after the wrapper, on `a3c_<slave>_axi_*` nets, as the last stage before the pins.
4. Handles CDC if `cdc=true`. A slave that two or more masters reach takes per-master lane ports (`<slave>_axi_lane_{aw,w,ar}*`, sized and ordered by `bridge_pkg/cdc_lanes.py`) and instantiates `bridge_cdc_slave_arb`, which crosses the lanes and arbitrates on `s_aclk` (bridge W9); the crossbar emits the lanes instead of an arbiter for that slave (`CrossbarGenerator._generate_lane_routing`) and the bridge top wires them. A slave one master reaches inserts `axi4_cdc_{wr,rd}`.

## Crossbar (`CrossbarGenerator`)

The crossbar module wires all master-adapter outputs to all slave-adapter inputs. It contains:

- AW and AR request matrices.
- Per-slave round-robin arbiters (or QoS arbiters when `arbitration="qos"`).
- W-owner FIFOs and response routing by `bridge_id`.
- Optional registered crossbar stage when `xbar_pipeline=true`.
