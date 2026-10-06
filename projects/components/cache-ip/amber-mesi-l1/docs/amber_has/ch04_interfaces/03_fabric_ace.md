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

# Fabric-Side ACE Masters and Coherent Issue

## Onyx-rig fabric

`amber_ace` uses the existing `rtl/amba/ace/axi4ace_master_rd` and `axi4ace_master_wr` modules toward `onyx`. These are full ACE masters with `ARSNOOP[3:0]` and `AWSNOOP[2:0]` transaction-type fields and auto-pulsed `RACK`/`WACK` outputs.

## `amber_ace_issue`

`amber_ace_issue` maps cache-side events to the onyx D2 coherent-transaction subset:

| Cache event | ACE transaction | Snoop field |
|---|---|---|
| read miss, shared intent | `ReadShared` | `fub_axi_arsnoop[3:0]` = `ReadShared` encoding |
| read miss, exclusive intent | `ReadUnique` | `fub_axi_arsnoop[3:0]` = `ReadUnique` encoding |
| write to Shared line | `CleanUnique` | `fub_axi_awsnoop[2:0]` = `CleanUnique` encoding |
| write to Invalid line (whole line) | `MakeUnique` | `fub_axi_awsnoop[2:0]` = `MakeUnique` encoding |
| dirty eviction | `WriteBack` | `fub_axi_awsnoop[2:0]` = `WriteBack` encoding |
| clean eviction | `Evict` | `fub_axi_awsnoop[2:0]` = `Evict` encoding |

: Table 4.2: Cache events to ACE transactions

## Real ACE master read port (`axi4ace_master_rd`)

The upstream (cache) side uses the `fub_axi_*` prefix; the master side uses `m_axi_*`:

| Signal | Direction | Width | Notes |
|---|---|---|---|
| `fub_axi_arid` | in | `AXI_ID_WIDTH` | upstream AR ID |
| `fub_axi_araddr` | in | `AXI_ADDR_WIDTH` | AR address |
| `fub_axi_arlen` | in | 8 | AR burst length |
| `fub_axi_arsize` | in | 3 | AR burst size |
| `fub_axi_arburst` | in | 2 | AR burst type |
| `fub_axi_arlock` | in | 1 | AR lock |
| `fub_axi_arcache` | in | 4 | AR cache hint |
| `fub_axi_arprot` | in | 3 | AR protection |
| `fub_axi_arqos` | in | 4 | AR QoS |
| `fub_axi_arregion` | in | 4 | AR region |
| `fub_axi_aruser` | in | `AXI_USER_WIDTH` | AR user |
| `fub_axi_arsnoop[3:0]` | in | 4 | **ACE transaction type** |
| `fub_axi_arvalid` | in | 1 | AR valid |
| `fub_axi_arready` | out | 1 | AR ready |
| `fub_axi_rid` | out | `AXI_ID_WIDTH` | R ID |
| `fub_axi_rdata` | out | `AXI_DATA_WIDTH` | R data |
| `fub_axi_rresp` | out | 2 | R response |
| `fub_axi_rlast` | out | 1 | R last |
| `fub_axi_ruser` | out | `AXI_USER_WIDTH` | R user |
| `fub_axi_rvalid` | out | 1 | R valid |
| `fub_axi_rready` | in | 1 | R ready |
| `m_axi_ar*` | out/in | — | master-side AR mirror of `fub_axi_ar*` |
| `m_axi_r*` | in/out | — | master-side R mirror of `fub_axi_r*` |
| `m_axi_rack` | out | 1 | **ACE read acknowledge**, auto-pulsed one cycle after last R beat |
| `busy` | out | 1 | activity status for clock gating |

: Table 4.3: `axi4ace_master_rd` pin contract

## Real ACE master write port (`axi4ace_master_wr`)

| Signal | Direction | Width | Notes |
|---|---|---|---|
| `fub_axi_awid` | in | `AXI_ID_WIDTH` | upstream AW ID |
| `fub_axi_awaddr` | in | `AXI_ADDR_WIDTH` | AW address |
| `fub_axi_awlen` | in | 8 | AW burst length |
| `fub_axi_awsize` | in | 3 | AW burst size |
| `fub_axi_awburst` | in | 2 | AW burst type |
| `fub_axi_awlock` | in | 1 | AW lock |
| `fub_axi_awcache` | in | 4 | AW cache hint |
| `fub_axi_awprot` | in | 3 | AW protection |
| `fub_axi_awqos` | in | 4 | AW QoS |
| `fub_axi_awregion` | in | 4 | AW region |
| `fub_axi_awuser` | in | `AXI_USER_WIDTH` | AW user |
| `fub_axi_awsnoop[2:0]` | in | 3 | **ACE transaction type** |
| `fub_axi_awvalid` | in | 1 | AW valid |
| `fub_axi_awready` | out | 1 | AW ready |
| `fub_axi_wdata` | in | `AXI_DATA_WIDTH` | W data |
| `fub_axi_wstrb` | in | `AXI_WSTRB_WIDTH` | W strobe |
| `fub_axi_wlast` | in | 1 | W last |
| `fub_axi_wuser` | in | `AXI_USER_WIDTH` | W user |
| `fub_axi_wvalid` | in | 1 | W valid |
| `fub_axi_wready` | out | 1 | W ready |
| `fub_axi_bid` | out | `AXI_ID_WIDTH` | B ID |
| `fub_axi_bresp` | out | 2 | B response |
| `fub_axi_buser` | out | `AXI_USER_WIDTH` | B user |
| `fub_axi_bvalid` | out | 1 | B valid |
| `fub_axi_bready` | in | 1 | B ready |
| `m_axi_aw*` / `m_axi_w*` / `m_axi_b*` | — | — | master-side AW/W/B mirrors |
| `m_axi_wack` | out | 1 | **ACE write acknowledge**, auto-pulsed one cycle after B handshake |
| `busy` | out | 1 | activity status for clock gating |

: Table 4.4: `axi4ace_master_wr` pin contract

`RACK` and `WACK` are auto-pulsed inside the adapters because the onyx D2 subset has no ordering semantics that require explicit master-controlled acknowledges.
