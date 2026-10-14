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

This chapter lists the top-level ports of `amber_top` and `amber_ace_top`. Internal `l1_core` ports are defined in the per-block chapters of Chapter 2.

---

## `amber_top` — Pair-Rig Top

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

Plain AXI4 masters driven by `l1_fill` and `l1_drain` through the house `axi4_master_rd_monlite` / `axi4_master_wr_monlite` wrappers, whose signal names and widths they follow.

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

## `amber_ace_top` — Onyx-Rig Top

`amber_ace_top` has the same CPU GAXI slave, snoop responder, and MonBus ports as `amber_top`. The memory-side masters are full ACE masters with `ARSNOOP` / `AWSNOOP`, `ARDOMAIN` / `AWDOMAIN` and `ARBAR` / `AWBAR` fields, the 4-bit ACE `RRESP` (IHI 0022H §D2.1), and auto-pulsed `RACK` / `WACK` outputs (deprecated per ruling 2026-10-11 (Sean); removal tracked as amber A5). `amber_ace_issue` maps cache-side events to ACE transactions; see Chapter 2.8.

| Signal | Direction | Width | Description |
|--------|-----------|-------|-------------|
| `m_axi_arsnoop` | output | 4 | ACE read transaction type |
| `m_axi_ardomain` | output | 2 | Shareability domain; tied to `0b10` Outer Shareable |
| `m_axi_arbar` | output | 2 | Barrier type; tied to `0b00`, normal access (amber issues no barriers) |
| `m_axi_rresp` | input | 4 | `[1:0]` AXI response, `[2]` PassDirty, `[3]` IsShared; the core consumes `[1:0]` only (Chapter 3.3) |
| `m_axi_rack` | output | 1 | ACE read acknowledge (auto-pulsed) |
| `m_axi_awsnoop` | output | 3 | ACE write transaction type |
| `m_axi_awdomain` | output | 2 | Shareability domain; tied to `0b10` Outer Shareable |
| `m_axi_awbar` | output | 2 | Barrier type; tied to `0b00`, normal access |
| `m_axi_wack` | output | 1 | ACE write acknowledge (auto-pulsed) |

All other AXI/ACE master signals mirror `amber_top` but connect to `axi4ace_master_rd_monlite` / `axi4ace_master_wr_monlite` instead of the plain AXI4 wrappers.

---

## Parameters

All geometry, policy, and bus-width choices are elaboration parameters. See Chapter 6 and the HAS [parameters chapter](../../amber_has/ch05_parameters/01_parameters.md) for the complete list. There is no runtime register block.

---

**Last Updated:** 2026-10-11
