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

# Adapters and Crossbar

## Master adapter (`<name>_adapter.sv`)

The master adapter sits between an external master and the internal crossbar. Its responsibilities are:

- Expose the external port with the configured prefix and protocol.
- Insert timing-isolation wrappers when requested.
- Insert protocol converters for non-AXI4 master protocols (`apb`, `apb5`, `axil`, `axil5`, `wb4`, `axi3`, `axi5`).
- Generate per-width internal paths and instantiate width converters only where master and slave widths differ.
- Decode addresses and emit `slave_select_aw/ar` plus `bridge_id_aw/ar`.

### Per-width paths

For each unique slave width the master connects to, the adapter emits a separate internal AXI4 path. If the master width matches the slave width, the path is direct; otherwise it uses a converter. Example from `bridge_mix_e`:

```systemverilog
// cpu_axi3 Adapter outputs
logic [NUM_SLAVES-1:0] cpu_axi3_slave_select_aw;
logic [BRIDGE_ID_WIDTH-1:0] cpu_axi3_bridge_id_aw;
// 32b path
axi4_aw_t     cpu_axi3_32b_aw;
axi4_w_32b_t  cpu_axi3_32b_w;
// 64b path
axi4_aw_t     cpu_axi3_64b_aw;
axi4_w_64b_t  cpu_axi3_64b_w;
```

## Slave adapter (`<name>_adapter.sv`)

The slave adapter sits between the crossbar and an external slave. Its responsibilities are:

- Convert the internal AXI4 face to the external protocol.
- Carry the in-order `bridge_id` FIFO for response routing.
- Handle CDC if `cdc=true`.
- Expose APB, AXI-Lite, AXI3, AXI5, or Wishbone pins as configured.

### Response routing

Each slave adapter keeps an in-order FIFO of `bridge_id` values pushed on the address handshake and popped on the response. The returned AXI ID is **not** used for routing; the FIFO head determines which master receives the response.

## Crossbar (`<bridge_name>_xbar.sv`)

The crossbar module:

- Accepts per-master decode outputs (`slave_select_*`, `bridge_id_*`).
- Builds AW/AR request matrices.
- Instantiates per-slave round-robin arbiters with grant locked to the address handshake.
- Routes W beats via a per-slave W-owner FIFO.
- Muxes responses back to masters using the `bridge_id` sideband.
- Optionally inserts a registered stage when `xbar_pipeline=true`.

The crossbar is protocol-agnostic internally; all protocol conversion happens in the adapters.
