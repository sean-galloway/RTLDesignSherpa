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
- Handle CDC if `cdc=true`: `axi4_cdc_{wr,rd}` between the port (on `ext_aclk`) and the timing wrapper (on `aclk`). (A slave adapter does the same for one master; for several it takes the crossbar's per-master lanes into `bridge_cdc_slave_arb`, bridge W9.)
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
- Carry the response tracker: by ID (the ID's master-index bits and an outstanding counter) or an in-order `bridge_id` FIFO.
- Handle CDC if `cdc=true`.
- Insert `axi4_slave_watchdog` between the timing wrapper and the port (or the CDC) if `timeout_cycles > 0`, with `o_wdog_tripped` to the top's `<name>_timeout`.
- Expose APB, AXI-Lite, AXI3, AXI5, or Wishbone pins as configured.

### Response routing

Each slave adapter hands the crossbar the issuing master's index with every response. For an AXI3/AXI4/AXI5 slave in a bridge with more than one master (or any slave with `enable_ooo`) it routes by ID: slave-side AXI IDs are `{BRIDGE_ID, id}`, `clog2(NUM_MASTERS)` bits wider than the master's, so the index is the top bits of the returned BID/RID and the slave may complete different IDs out of order. Single-master bridges, protocol-shim slaves and the subtractive slave store the `bridge_id` on the address handshake in an in-order FIFO whose head names the master.

`SlaveAdapterGenerator` emits the by-ID form (`track_by_id`) as two counters, `wr_out_cnt` and `rd_out_cnt`, that count to the slave's `max_outstanding` and gate AWREADY / ARREADY when full, plus `bid_bridge_id` / `rid_bridge_id` assigned from the ID's prefix bits. Until 2026-10-18 it emitted a pair of `bridge_cam` instances instead. Their response lookup was the fabric's critical path, and they stored nothing the ID did not already carry (bridge W12, MAS 4.1). Changing this emission changes every by-ID slave adapter, so regenerate all bridges (`make regen`) and re-run the full regression (Chapter 5).

## Crossbar (`<bridge_name>_xbar.sv`)

The crossbar module:

- Accepts per-master decode outputs (`slave_select_*`, `bridge_id_*`).
- Builds AW/AR request matrices.
- On a slave that two or more masters reach, puts each master's AW and AR in its own registered request slot and arbitrates among the slots at the slave-side nets (round-robin or QoS, grant locked to the address handshake); a master's AW enters a slot only while none of its other slots holds one (the write ordering rule, MAS 2.4).
- Routes W beats via a per-slave W-owner FIFO, pushed at the AW pick. On an AXI slave with slots the FIFO's empty bypass hands W to the AW being presented; a shim slave (APB / AXI4-Lite / WB4, slotted since bridge W14) takes no bypass, since it does not accept W before its AW.
- Tells the slave adapter of an arbitrated AXI4/AXI5 slave to cut its AW/AR stage (`arbitrated=True`): the slots are that register.
- Muxes responses back to masters using the `bridge_id` sideband.
- Optionally inserts a registered stage when `xbar_pipeline=true`.

The crossbar is protocol-agnostic internally; all protocol conversion happens in the adapters.
