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

# Port Specification Schema

Each master and slave is described by a TOML table under `[[bridge.masters]]` or `[[bridge.slaves]]`. The loader converts each table into a `PortSpec` dataclass (`bridge_pkg/config.py`).

## Common port fields

| Field | Type | Default | `PortSpec` attribute | Description |
|-------|------|---------|----------------------|-------------|
| `name` | string | required | `port_name` | Unique identifier used in generated module names and file names. |
| `prefix` | string | required | `prefix` | Signal prefix. The generator normalizes a missing trailing underscore (`cpu_m_axi` → `cpu_m_axi_`). |
| `protocol` | string | required | `protocol` | One of `axi3`, `axi4`, `axi5`, `apb`, `apb5`, `axil`, `axil5`, `wb4`. |
| `channels` | string | required | `channels` | One of `rw`, `wr`, `rd`. Slaves must declare what they support; the generator trims unneeded channels. |
| `data_width` | int | required | `data_width` | Data bus width in bits. |
| `addr_width` | int | required | `addr_width` | Address bus width in bits. |
| `id_width` | int | `0` | `id_width` | AXI ID width. Required > 0 for `axi4`/`axi5` masters; must be 0 for APB, AXI-Lite, and Wishbone. |
| `user_width` | int | `0` | (passed to wrapper) | AXI4 user signal width. |
| `cdc` | boolean | `false` | `cdc` | Run this port on its own clock (`<name>_aclk` / `<name>_aresetn`) behind `axi4_cdc_{wr,rd}`: on a slave between the timing wrapper and the port, on a master between the port and the timing wrapper (GitHub #119 L2). A slave several masters reach is crossed per master and arbitrated on its own clock instead (`bridge_cdc_slave_arb`, bridge W9), and takes no `timeout_cycles` or monitor. `protocol="axi4"` only. |

: Common port fields

## Slave-only fields

| Field | Type | Default | `PortSpec` attribute | Description |
|-------|------|---------|----------------------|-------------|
| `base_addr` | hex string/int | required for slaves | `base_addr` | Start of the slave address window. Must be 4 KiB-aligned. |
| `addr_range` | hex string/int | required for slaves | `addr_range` | Size of the slave window. Must be a non-zero multiple of 4 KiB. |
| `timeout_cycles` | int | `0` | `timeout_cycles` | > 0 puts `axi4_slave_watchdog` in front of this AXI4 slave (DECERR for everything after that many silent cycles; top output `<name>_timeout`). 0 or >= 2. GitHub #119 L3. |

: Slave-only fields

## Optional behavior fields

| Field | Type | Default | `PortSpec` attribute | Description |
|-------|------|---------|----------------------|-------------|
| `interface` | table | none | see below | Timing-isolation wrapper configuration. |
| `enable_ooo` | boolean | `false` | `enable_ooo` | Mark slave as out-of-order capable. (No generated fixture currently uses this.) |
| `max_outstanding` | int, power of two 2..64 | `[bridge].max_outstanding` (16) | `max_outstanding` | This port's outstanding limit per direction (master: tracker depth; slave: response-tracker depth). The internal subtractive slave stays at 16. |
| `use_monitor` | boolean | `true` | `use_monitor` | Per-port monitor enable; meaningful only for `"mon"` variants. |
| `mon_add` | list of strings | `[]` | `mon_add` | Additive reporter cones beyond the preset. Names come from `MON_CONES`: `error`, `timeout`, `compl`, `threshold`, `perf`, `debug`. |
| `mon_remove` | list of strings | `[]` | `mon_remove` | Reporter cones to remove from the preset. |
| `axi5_features` | list of strings | `[]` | `axi5_features` | AXI5 sideband feature list. Legal only on `axi5` or `axil5` ports. |
| `internal` | boolean | `false` | `internal` | Port has no top-level pins. Used automatically for the subtractive catch-all. |

: Optional behavior fields

## `axi5_features` values

The validator (`bridge_pkg/config_validator.py`) accepts:

- Droppable sideband: `nsaid`, `trace`, `mpam`, `mecid`, `unique`, `chunking`.
- Connectivity-gated (every connected path must be native AXI5, same feature, same width): `poison`, `atomic`, `mte`.

On `axil5` ports, only `user` and `exclusive` are forwardable; `trace`, `loop`, `mpam`, `mecid`, `nsaid`, `poison` are rejected because they have no AXI4 source/destination.

## Channel semantics

| `channels` | Master gets | Slave must support |
|------------|-------------|--------------------|
| `rw` | AW, W, B, AR, R | AW, W, B, AR, R |
| `wr` | AW, W, B only | AW, W, B |
| `rd` | AR, R only | AR, R |

: Channel semantics

A `wr` master may connect to a `wr` or `rw` slave; a `rd` master may connect to a `rd` or `rw` slave. A `wr` master cannot connect to a `rd` slave, and vice versa.

## Example

```toml
[[bridge.masters]]
name       = "cpu"
prefix     = "cpu_m_axi_"
protocol   = "axi4"
channels   = "rw"
id_width   = 4
addr_width = 32
data_width = 64
user_width = 1

[[bridge.slaves]]
name       = "ddr"
prefix     = "ddr_s_axi_"
protocol   = "axi4"
channels   = "rw"
id_width   = 6
addr_width = 32
data_width = 512
user_width = 1
base_addr  = "0x00000000"
addr_range = "0x80000000"
```
