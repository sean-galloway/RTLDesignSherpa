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

# Bridge-Level TOML Keys

The TOML `[bridge]` table configures the bridge as a whole. It is parsed by `bridge_pkg.config_loader.load_config()` into the `BridgeConfig` dataclass (`bridge_pkg/config.py`).

## `[bridge]` scalar keys

| Key | Type | Default | Dataclass field | Description |
|-----|------|---------|-----------------|-------------|
| `name` | string | `""` | `BridgeConfig.name` | Output base name. If empty, the generator auto-names from topology (`bridge_<M>x<S>_<channels>`). |
| `variants` | list of strings | `["no"]` | `BridgeConfig.variants` | Build variants to emit. Each entry must be `"no"` or `"mon"`. At least one entry is required in TOML. |
| `description` | string | `""` | ignored | Human-readable comment; copied into generated header only. |

: [bridge] scalar keys

## `[bridge.clock]` table

| Key | Type | Default | Used by | Description |
|-----|------|---------|---------|-------------|
| `name` | string | `"aclk"` | header comment | Clock signal name (informational). |
| `frequency_mhz` | int | none | header comment | Clock frequency (informational). |

: [bridge.clock] table

## Crossbar and arbitration keys

| Key | Type | Default | Dataclass field | Description |
|-----|------|---------|-----------------|-------------|
| `xbar_pipeline` | boolean | `false` | `BridgeConfig.xbar_pipeline` | Add skid register stage on every slave-side channel inside the crossbar. |
| `preset` | string | none | defaults for `PortSpec.latency`, `PortSpec.rate_buffer`, `PortSpec.id_remap` | `"xbar"` only: `latency = "cut_none"` on every same-clock axi4/axi5 port, `rate_buffer = 0`, `id_remap = false`. Defaults only: a `[bridge]` key or a port key of the same name wins, and a converted or CDC port keeps `cut_all`. Any other name is a `ValueError` at load (`config_loader._PRESETS`). |
| `id_remap` | boolean | `true` (`false` under `preset = "xbar"`) | `PortSpec.id_remap` (default for every master) | `false` keeps each master's own ID: `width_utils.id_remapped` is false, no `bridge_id_remap` is built, and `xbar_id_width` becomes index bits plus the widest master ID. A master entry may set its own. A non-boolean is a `ValueError`. |
| `arbitration` | string | `"rr"` | `BridgeConfig.arbitration` | Per-slave arbitration policy. `"rr"` = round-robin; `"qos"` = QoS + aging. |
| `qos_aging_shift` | int | `4` | `BridgeConfig.qos_aging_shift` | For `"qos"`, a waiting request gains one priority level every `2**shift` cycles. |
| `id_track_bits` | int 0..8 | `4` | `BridgeConfig.id_track_bits` | Per-ID target table in a master adapter that keeps its port's ID (`width_utils.id_remapped` false; a remapped port uses `bridge_id_remap` instead): `2**id_track_bits` entries by the ID's low bits (never more than the port's ID). A request waits only while its ID is in flight to a different slave. Fixes the one-target-per-master limitation (GitHub #119 L1). Out of range is a `ValueError` at load. |
| `max_outstanding` | int, power of two 2..64 | `16` | `PortSpec.max_outstanding` (default for every port) | Outstanding-transaction limit per direction for every port that does not set its own: master-adapter tracker depth, per-ID count width, and the remap slot width `$clog2(max_outstanding)` (which sets `XBAR_ID_WIDTH` for a master whose ID is wider); slave-adapter by-ID counter / in-order FIFO depth; the crossbar's W-destination (per master path) and W-owner (per slave, plus 2 on a registered crossbar) FIFOs follow. Fixes the fixed 16 (GitHub #119 L5). |

: Crossbar and arbitration keys

## Monitor and cfg subsystem keys

| Key | Type | Default | Dataclass field | Description |
|-----|------|---------|-----------------|-------------|
| `mon_preset` | string | `"lite"` | `BridgeConfig.mon_preset` | Baseline monitor reporter enables. Accepted aliases: `"all"`, `"error_only"`, `"functional"`, `"none"`, `"lite"`. Since 2026-09-26 every monitored port uses `axi_monitor_lite`, so the preset resolves to the lite set regardless. |
| `use_all_monitors` | boolean | `false` | `BridgeConfig.use_all_monitors` | Force `USE_MONITOR=1` on every port. Mutually exclusive with `use_no_monitors`. |
| `use_no_monitors` | boolean | `false` | `BridgeConfig.use_no_monitors` | Force `USE_MONITOR=0` on every port. Mutually exclusive with `use_all_monitors`. |
| `internal_axil_group` | boolean | `true` | `BridgeConfig.internal_axil_group` | For `"mon"` variants, instantiate the internal `monbus_axil4_axil4_group`. When `false`, expose the aggregated monbus stream at the top. |
| `use_cfg_regblock` | boolean | `false` | `BridgeConfig.use_cfg_regblock` | Replace the 350+ individual `cfg_*` top-level pins with a PeakRDL-generated cfg register block. |

: Monitor and cfg subsystem keys

## `[bridge.mon_group]` table

| Key | Type | Default | Dataclass field | Description |
|-----|------|---------|-----------------|-------------|
| `slave_protocol` | string | `"axil4"` | `MonGroupConfig.slave_protocol` | Protocol of the monbus group slave-read port. `"axil4"` or `"axi4"`. Deprecated spelling `"axil"` is normalized to `"axil4"`. |
| `master_protocol` | string | `"axil4"` | `MonGroupConfig.master_protocol` | Protocol of the monbus group master-write port. `"axil4"` or `"axi4"`. |
| `axi_id_width` | int | `8` | `MonGroupConfig.axi_id_width` | AXI ID width when either side is `axi4`. |
| `max_burst_beats` | int | `64` | `MonGroupConfig.max_burst_beats` | Max write burst when master side is `axi4`. |
| `fifo_depth_err` | int | `64` | `MonGroupConfig.fifo_depth_err` | Error FIFO depth. |
| `fifo_depth_write` | int | `96` | `MonGroupConfig.fifo_depth_write` | Write-data FIFO depth in beats. |
| `flush_timeout_cycles` | int | `1024` | `MonGroupConfig.flush_timeout_cycles` | Flush timeout. |
| `use_compression` | int | `0` | `MonGroupConfig.use_compression` | Compression enable. |

: [bridge.mon_group] table

## `[bridge.defaults]` table

The `defaults.skid_depths` sub-table provides default skid depths for interface wrappers:

```toml
[bridge.defaults]
skid_depths = {ar = 2, r = 4, aw = 2, w = 4, b = 2}
```

Per-port `interface.skid_depths` overrides these defaults, and a port's `latency` mode then sets the channels it cuts to 0 (pass-through). Valid per-channel depths are integers in the range `2..8` inclusive. Until GitHub #119 L7 (2026-10-15) both tables were parsed and ignored -- every wrapper was built 2/4/2/2/2; they take effect now. Any other key under `[bridge.defaults]` is reported and ignored.
