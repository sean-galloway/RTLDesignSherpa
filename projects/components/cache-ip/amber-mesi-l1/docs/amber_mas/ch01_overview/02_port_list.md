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

# Top-Level Port List

This chapter lists the top-level ports of `amber` and `amber_ace`. Internal `amber_core` ports are defined in the per-block chapters of Chapter 2.

---

## `amber` — Pair-Rig Top

### Clock and Reset

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `aclk` | input | 1 | System clock |
| `aresetn` | input | 1 | Active-low asynchronous reset, synchronous deassert |

### CPU GAXI Slave

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `cpu_req_wr_valid` | input | 1 | CPU request valid |
| `cpu_req_wr_ready` | output | 1 | Cache ready to accept request |
| `cpu_req_wr_data` | input | `CPU_REQ_W` | Packed {addr, we, be, wdata} |
| `cpu_rsp_rd_valid` | output | 1 | Cache response valid |
| `cpu_rsp_rd_ready` | input | 1 | CPU ready to accept response |
| `cpu_rsp_rd_data` | output | `CPU_RSP_W` | Packed {rdata} |

### AXI4 Memory Masters

Plain AXI4 masters driven by `amber_fill` and `amber_drain`. Signal names and widths follow the house `axi4_master_rd` / `axi4_master_wr` wrappers.

| Channel | Direction | Signals |
|---------|-----------|---------|
| AR | out | `m_axi_arid`, `m_axi_araddr`, `m_axi_arlen`, `m_axi_arsize`, `m_axi_arburst`, `m_axi_arlock`, `m_axi_arcache`, `m_axi_arprot`, `m_axi_arqos`, `m_axi_arregion`, `m_axi_aruser`, `m_axi_arvalid` |
| R | in/out | `m_axi_rid`, `m_axi_rdata`, `m_axi_rresp`, `m_axi_rlast`, `m_axi_ruser`, `m_axi_rvalid`, `m_axi_rready` |
| AW | out | `m_axi_awid`, `m_axi_awaddr`, `m_axi_awlen`, `m_axi_awsize`, `m_axi_awburst`, `m_axi_awlock`, `m_axi_awcache`, `m_axi_awprot`, `m_axi_awqos`, `m_axi_awregion`, `m_axi_awuser`, `m_axi_awvalid` |
| W | out | `m_axi_wdata`, `m_axi_wstrb`, `m_axi_wlast`, `m_axi_wuser`, `m_axi_wvalid` |
| B | in/out | `m_axi_bid`, `m_axi_bresp`, `m_axi_buser`, `m_axi_bvalid`, `m_axi_bready` |

### ACE Snoop Responder

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_acaddr` | input | `ADDR_WIDTH` | Snoop address |
| `m_axi_acsnoop` | input | 4 | Snoop transaction type |
| `m_axi_acprot` | input | 3 | Snoop protection |
| `m_axi_acvalid` | input | 1 | Snoop address valid |
| `m_axi_acready` | output | 1 | Cache ready for snoop |
| `m_axi_crresp` | output | 5 | Snoop response |
| `m_axi_crvalid` | output | 1 | Snoop response valid |
| `m_axi_crready` | input | 1 | Snoop response ready |
| `m_axi_cddata` | output | `DATA_WIDTH` | Snoop data |
| `m_axi_cdlast` | output | 1 | Snoop data last beat |
| `m_axi_cdvalid` | output | 1 | Snoop data valid |
| `m_axi_cdready` | input | 1 | Snoop data ready |

### MonBus

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `mon_valid` | output | 1 | Monitor packet valid |
| `mon_ready` | input | 1 | Monitor consumer ready |
| `mon_packet` | output | 128 | Monitor packet |
| `mon_timestamp` | output | 64 | Side-band timestamp |

---

## `amber_ace` — Onyx-Rig Top

`amber_ace` has the same CPU GAXI slave, snoop responder, and MonBus ports as `amber`. The memory-side masters are full ACE masters with `ARSNOOP` / `AWSNOOP` fields and auto-pulsed `RACK` / `WACK` outputs. `amber_ace_issue` maps cache-side events to ACE transactions; see Chapter 2.8.

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_arsnoop` | output | 4 | ACE read transaction type |
| `m_axi_rack` | output | 1 | ACE read acknowledge (auto-pulsed) |
| `m_axi_awsnoop` | output | 3 | ACE write transaction type |
| `m_axi_wack` | output | 1 | ACE write acknowledge (auto-pulsed) |

All other AXI/ACE master signals mirror `amber` but connect to `axi4ace_master_rd` / `axi4ace_master_wr` instead of the plain AXI4 wrappers.

---

## Parameters

All geometry, policy, and bus-width choices are elaboration parameters. See Chapter 6 and the HAS [parameters chapter](../../amber_has/ch05_parameters/01_parameters.md) for the complete list. There is no runtime register block.

---

**Last Updated:** 2026-10-06
