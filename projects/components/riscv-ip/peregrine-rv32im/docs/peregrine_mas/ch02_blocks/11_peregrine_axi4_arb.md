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

# peregrine_axi4_arb

**Module:** `peregrine_axi4_arb.sv`

## Responsibility

peregrine's house AXI4 arbiter (PRD P7): `NM` masters onto one fabric port. No N:1 AXI4 merge existed in `rtl/amba`, so this one is built on `arbiter_round_robin` from `rtl/common`.

## Parameters

<!-- GEN:params:peregrine_axi4_arb -->

| Parameter | Kind | Type | Default | Description |
|----------------|----------|------------|--------------|------------------------------|
| `NM` | parameter | `int` | `3` | Number of masters (>= 2) |
| `AXI_DW` | parameter | `int` | `64` | Data width |
| `AXI_IW` | parameter | `int` | `4` | Master-side id width |
| `MI_W` | localparam | `int` | `$clog2(NM)` | Master index width (derived) |
| `FIW` | localparam | `int` | `AXI_IW + MI_W` | Fabric id width, AXI_IW + MI_W (derived) |

: peregrine_axi4_arb parameters

<!-- /GEN -->

## Ports

<!-- GEN:ports:peregrine_axi4_arb -->

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `clk` | input | `1` | Clock |
| `rst_n` | input | `1` | Reset |
| `s_axi_arid` | input | `[NM*AXI_IW-1:0]` | Read address id (per master, flattened) |
| `s_axi_araddr` | input | `[NM*32-1:0]` | Read address (per master, flattened) |
| `s_axi_arlen` | input | `[NM*8-1:0]` | Burst length - 1 (per master, flattened) |
| `s_axi_arsize` | input | `[NM*3-1:0]` | Beat size (log2 bytes) (per master, flattened) |
| `s_axi_arburst` | input | `[NM*2-1:0]` | Burst type (per master, flattened) |
| `s_axi_arvalid` | input | `[NM-1:0]` | Read address valid (per master, flattened) |
| `s_axi_arready` | output | `[NM-1:0]` | Read address ready (per master, flattened) |
| `s_axi_rid` | output | `[NM*AXI_IW-1:0]` | Read data id (per master, flattened) |
| `s_axi_rdata` | output | `[NM*AXI_DW-1:0]` | Read data beat (per master, flattened) |
| `s_axi_rresp` | output | `[NM*2-1:0]` | Read response (per master, flattened) |
| `s_axi_rlast` | output | `[NM-1:0]` | Last read beat (per master, flattened) |
| `s_axi_rvalid` | output | `[NM-1:0]` | Read data valid (per master, flattened) |
| `s_axi_rready` | input | `[NM-1:0]` | Read data ready (per master, flattened) |
| `s_axi_awid` | input | `[NM*AXI_IW-1:0]` | Write address id (per master, flattened) |
| `s_axi_awaddr` | input | `[NM*32-1:0]` | Write address (per master, flattened) |
| `s_axi_awlen` | input | `[NM*8-1:0]` | Burst length - 1 (per master, flattened) |
| `s_axi_awsize` | input | `[NM*3-1:0]` | Beat size (log2 bytes) (per master, flattened) |
| `s_axi_awburst` | input | `[NM*2-1:0]` | Burst type (per master, flattened) |
| `s_axi_awvalid` | input | `[NM-1:0]` | Write address valid (per master, flattened) |
| `s_axi_awready` | output | `[NM-1:0]` | Write address ready (per master, flattened) |
| `s_axi_wdata` | input | `[NM*AXI_DW-1:0]` | Write data beat (per master, flattened) |
| `s_axi_wstrb` | input | `[NM*STRBW-1:0]` | Write byte strobes (per master, flattened) |
| `s_axi_wlast` | input | `[NM-1:0]` | Last write beat (per master, flattened) |
| `s_axi_wvalid` | input | `[NM-1:0]` | Write data valid (per master, flattened) |
| `s_axi_wready` | output | `[NM-1:0]` | Write data ready (per master, flattened) |
| `s_axi_bid` | output | `[NM*AXI_IW-1:0]` | Write response id (per master, flattened) |
| `s_axi_bresp` | output | `[NM*2-1:0]` | Write response (per master, flattened) |
| `s_axi_bvalid` | output | `[NM-1:0]` | Write response valid (per master, flattened) |
| `s_axi_bready` | input | `[NM-1:0]` | Write response ready (per master, flattened) |
| `m_axi_arid` | output | `[FIW-1:0]` | Read address id |
| `m_axi_araddr` | output | `[31:0]` | Read address |
| `m_axi_arlen` | output | `[7:0]` | Burst length - 1 |
| `m_axi_arsize` | output | `[2:0]` | Beat size (log2 bytes) |
| `m_axi_arburst` | output | `[1:0]` | Burst type |
| `m_axi_arlock` | output | `1` | Driven 0 |
| `m_axi_arcache` | output | `[3:0]` | Driven 0 |
| `m_axi_arprot` | output | `[2:0]` | Driven 0 |
| `m_axi_arqos` | output | `[3:0]` | Driven 0 |
| `m_axi_arregion` | output | `[3:0]` | Driven 0 |
| `m_axi_arvalid` | output | `1` | Read address valid |
| `m_axi_arready` | input | `1` | Read address ready |
| `m_axi_rid` | input | `[FIW-1:0]` | Read data id |
| `m_axi_rdata` | input | `[AXI_DW-1:0]` | Read data beat |
| `m_axi_rresp` | input | `[1:0]` | Read response |
| `m_axi_rlast` | input | `1` | Last read beat |
| `m_axi_rvalid` | input | `1` | Read data valid |
| `m_axi_rready` | output | `1` | Read data ready |
| `m_axi_awid` | output | `[FIW-1:0]` | Write address id |
| `m_axi_awaddr` | output | `[31:0]` | Write address |
| `m_axi_awlen` | output | `[7:0]` | Burst length - 1 |
| `m_axi_awsize` | output | `[2:0]` | Beat size (log2 bytes) |
| `m_axi_awburst` | output | `[1:0]` | Burst type |
| `m_axi_awlock` | output | `1` | Driven 0 |
| `m_axi_awcache` | output | `[3:0]` | Driven 0 |
| `m_axi_awprot` | output | `[2:0]` | Driven 0 |
| `m_axi_awqos` | output | `[3:0]` | Driven 0 |
| `m_axi_awregion` | output | `[3:0]` | Driven 0 |
| `m_axi_awvalid` | output | `1` | Write address valid |
| `m_axi_awready` | input | `1` | Write address ready |
| `m_axi_wdata` | output | `[AXI_DW-1:0]` | Write data beat |
| `m_axi_wstrb` | output | `[STRBW-1:0]` | Write byte strobes |
| `m_axi_wlast` | output | `1` | Last write beat |
| `m_axi_wvalid` | output | `1` | Write data valid |
| `m_axi_wready` | input | `1` | Write data ready |
| `m_axi_bid` | input | `[FIW-1:0]` | Write response id |
| `m_axi_bresp` | input | `[1:0]` | Write response |
| `m_axi_bvalid` | input | `1` | Write response valid |
| `m_axi_bready` | output | `1` | Write response ready |

: peregrine_axi4_arb ports

<!-- /GEN -->

## Behavior

- **AR and AW** are arbitrated independently, each by `arbiter_round_robin` in ACK mode: the grant is registered and held until the granted address handshake, so the selected master's address is stable while it waits. Grant latency is one cycle from a master's valid to the fabric valid.
- **Ids.** The fabric id is `{master index, master id}`. R and B return to the master named by the index, so reads from different masters may be in flight together.
- **W follows AW.** An AW grant makes its master the W owner until its `wlast` beat, and no other AW is granted meanwhile. Writes are serialized; every master here has at most one write in flight, so this costs nothing and needs no W-order FIFO.
- **Unused fields.** `AxLOCK`, `AxCACHE`, `AxPROT`, `AxQOS` and `AxREGION` are not carried and are driven 0 on the fabric port.

---

**Last Updated:** 2026-11-25
