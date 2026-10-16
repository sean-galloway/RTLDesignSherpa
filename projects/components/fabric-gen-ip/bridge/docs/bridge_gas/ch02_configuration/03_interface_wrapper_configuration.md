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

# Interface Wrapper Configuration

The optional per-port `interface` table selects a timing-isolation wrapper and its skid depths. If omitted, the port is connected directly to the crossbar (no wrapper).

## `interface.type` values

| Value | Wrapper instantiated |
|-------|----------------------|
| `axi4_master` | `axi4_slave_wr` / `axi4_slave_rd` (master port acts as AXI slave to external master) |
| `axi4_slave` | `axi4_master_wr` / `axi4_master_rd` (slave port acts as AXI master to external slave) |
| `axi4_master_mon` | `_monlite` variant of the master wrapper |
| `axi4_slave_mon` | `_monlite` variant of the slave wrapper |

: interface.type values

The `_monlite` wrappers are used unconditionally since 2026-09-26; the old non-lite wrappers were retired.

## `interface.skid_depths` table

| Key | Type | Default | Valid range | Description |
|-----|------|---------|-------------|-------------|
| `ar` | int | from `[bridge.defaults.skid_depths]` | 2..8 | Read address skid depth. |
| `r` | int | from defaults | 2..8 | Read data skid depth. |
| `aw` | int | from defaults | 2..8 | Write address skid depth. |
| `w` | int | from defaults | 2..8 | Write data skid depth. |
| `b` | int | from defaults | 2..8 | Write response skid depth. |

: interface.skid_depths table

## `latency` (port key)

`latency` selects which channels of the port's timing wrapper are registered
(GitHub #119 L7). A cut channel's skid depth becomes 0, which
`gaxi_skid_buffer` builds as a combinational pass-through.

| Value | Registered channels | Port adds |
|-------|---------------------|-----------|
| `cut_all` (default) | AW, W, B, AR, R | 1 cycle per direction |
| `cut_ax` | AW, AR | 1 cycle on requests, 0 on W / B / R |
| `cut_none` | none | 0 cycles: the port boundary is wires |

: latency modes

Legal only on a same-clock `axi4` / `axi5` port; a converted port (AXI-Lite,
APB, Wishbone, AXI3) or a `cdc = true` port has buffers of its own that the
mode does not reach, so the loader rejects it there. The master adapter keeps
the resolved depths as module parameters (`SKID_DEPTH_*`), so a single
generated adapter can still be re-timed by overriding them at elaboration.
Measured on `bridge_2x2_rw_lat` by `test_bridge_2x2_rw_lat_modes`.

Example:

```toml
[[bridge.masters]]
name = "dma"
prefix = "dma_m_axi_"
protocol = "axi4"
channels = "rw"
id_width = 4
addr_width = 32
data_width = 512
user_width = 1
interface = {type = "axi4_master", skid_depths = {ar = 4, r = 8, aw = 4, w = 8, b = 4}}
```

## How the wrapper selection flows

1. `bridge_pkg/config_loader.py` reads the `interface` table into `PortSpec` attributes.
2. `bridge_generator.py` passes the port protocol and `use_monitor` flag to `BridgeModuleGenerator`.
3. `AdapterGenerator` (`bridge_pkg/generators/adapter_generator.py`) and `SlaveAdapterGenerator` (`bridge_pkg/generators/slave_adapter_generator.py`) instantiate the appropriate wrapper module based on protocol and monitor state.
4. The generated adapter module wires the wrapper's `fub_axi_*` internal face to the crossbar.

## Protocol-specific wrapper notes

- `axi5` ports use `axi5_slave_{wr,rd}` on master sides and `axi5_master_{wr,rd}` on slave sides.
- `apb`/`apb5` master ports use `apb{4,5}_to_axi4` front-end converters inside the adapter.
- `wb4` master ports use `wb4_to_axi4`.
- `axi3` master ports use `axi3_to_axi4`.
- `apb`, `apb5`, `axil`, `axil5`, `wb4`, and `axi3` slave ports use the corresponding completer shim (`axi4_to_apb4_shim`, `axi4_to_wb4`, etc.).
