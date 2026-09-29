# signal_naming.py -- the one place external port names come from

**Scope:** mechanics of `bridge_pkg/signal_naming.py` for a reader of this
directory. Replaces `SIGNAL_NAMING_INTEGRATION.md` and
`SIGNAL_NAMING_QUICK_REF.md` (2026-09-29, bridge TASK-012): both showed a
`cpu_m_axi_awid` style the module has not produced since TASK-011, and they
named functions (`validate_signal_name`, `generate_master_ports`) that do not
exist. Every example below was executed against the module on 2026-09-29.

Consumers: `generators/adapter_generator.py`,
`generators/slave_adapter_generator.py`, `generators/crossbar_generator.py`,
`components/bridge_module_generator.py`. None of them builds a port name by
hand; if you need one, call this module.

## Import

```python
from bridge_pkg.signal_naming import (SignalNaming, Direction, AXI4Channel,
                                      Protocol, PortDirection, SignalInfo,
                                      AXI4_MASTER_SIGNALS, AXI4_SLAVE_SIGNALS,
                                      APB_MASTER_SIGNALS, APB_SLAVE_SIGNALS)
```

## Enums

| Enum | Values | Meaning |
|---|---|---|
| `Protocol` | `AXI4`, `APB` | protocol family of a port |
| `Direction` | `MASTER`, `SLAVE` | the BRIDGE's side: `MASTER` = the bridge presents a master-facing (slave) interface to an external master; `SLAVE` = the bridge drives an external slave |
| `AXI4Channel` | `AW`, `W`, `B`, `AR`, `R` | `.value` is the lowercase channel token used in names |
| `PortDirection` | `INPUT`, `OUTPUT` | direction of one signal from the bridge interface's perspective |

## `SignalInfo` (dataclass)

Fields: `name`, `direction: PortDirection`, `width_expr` (e.g. `"ADDR_WIDTH"`,
`"8"`, `"1"`), `width_param` (parameter name when parameterised, else
`None`), `is_vector`, `description`.

- `get_range(width_values: dict) -> str`: `"[31:0]"` for a vector given
  `{"ADDR_WIDTH": 32}`; `""` for a scalar; `"[EXPR-1:0]"` when the parameter
  is not in the dict. A width of 0 (the AXIL `id_width = 0` case) yields a
  1-bit scalar range rather than the invalid `[-1:0]`.
- `get_declaration(signal_name, width_values) -> str`: a full port
  declaration, e.g. `output  logic [31:0]  cpu_axi_awaddr`.

## `SignalNaming` (all static)

| Method | Returns |
|---|---|
| `axi4_signal_name(port_name, direction, channel, signal, prefix=None)` | `f"{prefix}{channel}{signal}"` when `prefix` is given (it must carry its own trailing underscore), else the legacy `f"{port_name}_axi_{channel}{signal}"` |
| `apb_signal_name(port_name, signal, prefix=None)` | `f"{prefix}{signal}"` or the legacy `f"{port_name}_{signal}"`; the signal token is passed through as given |
| `get_axi4_signal_info(direction, channel, signal) -> SignalInfo \| None` | the table entry for one signal |
| `get_apb_signal_info(direction, signal) -> SignalInfo \| None` | likewise for APB |
| `get_all_axi4_signals(port_name, direction, channels, prefix=None) -> dict[AXI4Channel, list[(name, SignalInfo)]]` | every signal of the requested channels, named |
| `get_all_apb_signals(port_name, direction, prefix=None) -> list[(name, SignalInfo)]` | the ten APB signals, named |
| `channels_from_type("rw" \| "wr" \| "rd") -> list[AXI4Channel]` | `[AW, W, B, AR, R]`, `[AW, W, B]`, `[AR, R]` |

`direction` selects the direction TABLE (`AXI4_MASTER_SIGNALS` vs
`AXI4_SLAVE_SIGNALS`, which differ only in `PortDirection`); it does not
change the name.

## Executed examples

```python
>>> SignalNaming.axi4_signal_name("cpu", Direction.MASTER, AXI4Channel.AW, "id")
'cpu_axi_awid'
>>> SignalNaming.axi4_signal_name("dma", Direction.MASTER, AXI4Channel.AR, "addr", prefix="dma_axil_")
'dma_axil_araddr'
>>> SignalNaming.apb_signal_name("apb0", "PSEL")
'apb0_PSEL'
>>> info = SignalNaming.get_axi4_signal_info(Direction.MASTER, AXI4Channel.AW, "addr")
>>> info.direction, info.width_expr, info.get_range({"ADDR_WIDTH": 32})
(<PortDirection.OUTPUT: 'output'>, 'ADDR_WIDTH', '[31:0]')
>>> info.get_declaration("cpu_axi_awaddr", {"ADDR_WIDTH": 32})
'output  logic [31:0]  cpu_axi_awaddr'
>>> sigs = SignalNaming.get_all_axi4_signals("cpu", Direction.MASTER, [AXI4Channel.AW, AXI4Channel.B])
>>> {ch: len(v) for ch, v in sigs.items()}
{<AXI4Channel.AW: 'aw'>: 13, <AXI4Channel.B: 'b'>: 5}
>>> [n for n, _ in sigs[AXI4Channel.AW]][:3]
['cpu_axi_awid', 'cpu_axi_awaddr', 'cpu_axi_awlen']
>>> [n for n, _ in SignalNaming.get_all_apb_signals("apb0", Direction.SLAVE)][:4]
['apb0_PSEL', 'apb0_PADDR', 'apb0_PENABLE', 'apb0_PWRITE']
>>> SignalNaming.channels_from_type("wr")
[<AXI4Channel.AW: 'aw'>, <AXI4Channel.W: 'w'>, <AXI4Channel.B: 'b'>]
```

## The tables

`AXI4_MASTER_SIGNALS` / `AXI4_SLAVE_SIGNALS`: `dict[AXI4Channel, dict[str,
SignalInfo]]` -- 13 AW, 6 W, 5 B, 13 AR and 7 R entries (the module is the
list; do not copy it here). `APB_MASTER_SIGNALS` /
`APB_SLAVE_SIGNALS`: `list[SignalInfo]` of the ten APB signals `PSEL PADDR
PENABLE PWRITE PWDATA PSTRB PPROT PRDATA PREADY PSLVERR`, the same names with
opposite `PortDirection`.

## Port generation pattern

```python
def emit_ports(port_name, channel_type, prefix, widths):
    for ch, sigs in SignalNaming.get_all_axi4_signals(
            port_name, Direction.MASTER,
            SignalNaming.channels_from_type(channel_type), prefix=prefix).items():
        for name, info in sigs:
            yield info.get_declaration(name, widths)
```

Where the rule came from: hand-built prefixes in the module generator once
connected the crossbar to signals that were never declared (bridge BUG-001);
the fix was to route every name through this module, and TASK-011 (Bug C)
added the per-port `prefix` override so a `.toml` can name its ports.
