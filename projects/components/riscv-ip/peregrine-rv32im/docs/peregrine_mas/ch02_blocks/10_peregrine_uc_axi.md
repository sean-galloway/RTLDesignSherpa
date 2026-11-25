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

# peregrine_uc_axi

**Module:** `peregrine_uc_axi.sv`

## Responsibility

The uncached data port (PRD P7): one 32-bit load or store at a time, as a single-beat AXI4 transaction on the fabric's data width. It serves the I/O window 0x1000_0000-0x1FFF_FFFF.

## Parameters

<!-- GEN:params:peregrine_uc_axi -->

| Parameter | Kind | Type | Default | Description |
|----------------|----------|------------|--------------|------------------------------|
| `AXI_DW` | parameter | `int` | `64` | Fabric data width, 32 or 64 |
| `AXI_IW` | parameter | `int` | `4` | AXI id width; the port always uses id 0 |

: peregrine_uc_axi parameters

<!-- /GEN -->

## Ports

<!-- GEN:ports:peregrine_uc_axi -->

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `clk` | input | `1` | Clock |
| `rst_n` | input | `1` | Reset |
| `req_valid` | input | `1` | Load or store request |
| `req_ready` | output | `1` | Idle: one transaction at a time |
| `req_addr` | input | `[31:0]` | Byte address |
| `req_we` | input | `1` | Store |
| `req_wstrb` | input | `[3:0]` | Byte strobes of the 32-bit word |
| `req_wdata` | input | `[31:0]` | Store word |
| `rsp_valid` | output | `1` | One-cycle response (a store's after B) |
| `rsp_rdata` | output | `[31:0]` | Load word, 0 outside rsp_valid |
| `m_axi_arid` | output | `[AXI_IW-1:0]` | Read address id |
| `m_axi_araddr` | output | `[31:0]` | Read address |
| `m_axi_arlen` | output | `[7:0]` | Burst length - 1 |
| `m_axi_arsize` | output | `[2:0]` | Beat size (log2 bytes) |
| `m_axi_arburst` | output | `[1:0]` | Burst type |
| `m_axi_arvalid` | output | `1` | Read address valid |
| `m_axi_arready` | input | `1` | Read address ready |
| `m_axi_rid` | input | `[AXI_IW-1:0]` | Read data id |
| `m_axi_rdata` | input | `[AXI_DW-1:0]` | Read data beat |
| `m_axi_rresp` | input | `[1:0]` | Read response |
| `m_axi_rlast` | input | `1` | Last read beat |
| `m_axi_rvalid` | input | `1` | Read data valid |
| `m_axi_rready` | output | `1` | Read data ready |
| `m_axi_awid` | output | `[AXI_IW-1:0]` | Write address id |
| `m_axi_awaddr` | output | `[31:0]` | Write address |
| `m_axi_awlen` | output | `[7:0]` | Burst length - 1 |
| `m_axi_awsize` | output | `[2:0]` | Beat size (log2 bytes) |
| `m_axi_awburst` | output | `[1:0]` | Burst type |
| `m_axi_awvalid` | output | `1` | Write address valid |
| `m_axi_awready` | input | `1` | Write address ready |
| `m_axi_wdata` | output | `[AXI_DW-1:0]` | Write data beat |
| `m_axi_wstrb` | output | `[STRBW-1:0]` | Write byte strobes |
| `m_axi_wlast` | output | `1` | Last write beat |
| `m_axi_wvalid` | output | `1` | Write data valid |
| `m_axi_wready` | input | `1` | Write data ready |
| `m_axi_bid` | input | `[AXI_IW-1:0]` | Write response id |
| `m_axi_bresp` | input | `[1:0]` | Write response |
| `m_axi_bvalid` | input | `1` | Write response valid |
| `m_axi_bready` | output | `1` | Write response ready |

: peregrine_uc_axi ports

<!-- /GEN -->

## Behavior

| State | Does | Leaves on |
|-------|------|-----------|
| `S_IDLE` | `req_ready = 1`; latch the word address, strobes and data on a request | A request: to `S_RD` (load) or `S_WR` (store) |
| `S_RD` | `arvalid` until accepted (AxSIZE 4 bytes, `arlen = 0`) | The R beat: `rsp_valid` next cycle with the word from its lane |
| `S_WR` | `awvalid` and `wvalid` together until each is accepted (in either order); strobes on the word's lanes | The B response: `rsp_valid` next cycle |

: peregrine_uc_axi states

- Stores are not posted: a store's response waits for B, so a store that retires has reached the fabric.
- `rsp_rdata` is driven 0 outside the `rsp_valid` cycle. A consumer that read it late would be relying on this port, not on the contract a D\$ also meets; driving 0 makes such a bug fail in the suites (TASK-001 stage 4).
- `rresp` and `bresp` are not reported: peregrine has no access-fault exception.

---

**Last Updated:** 2026-11-25
