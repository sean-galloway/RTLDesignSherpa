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

# CPU-Side GAXI Slave

## Interface decision

The CPU-side port is a GAXI slave (amber D2). We chose GAXI over a plain valid/ready native port and over an AXI4 slave because the house BFM/monitor coverage and skid/FIFO plumbing already exist, and STREAM can attach later without an adapter.

## Channel structure

The CPU-side port is **two house-GAXI streams** (amber D2) —
`wr_valid`/`wr_ready`/`wr_data` in, `rd_valid`/`rd_ready`/`rd_data` out.
The house GAXI pattern and its plumbing (`gaxi_skid_buffer`,
`gaxi_fifo_sync`) are documented with the `rtl/amba/gaxi/` modules, not
restated here. `amber_cpu_frontend` is the slave: it receives the
request stream and drives the response stream.

Request stream (CPU → amber, slave input):

| Signal | Direction | Width | Payload |
|---|---|---|---|
| `cpu_req_wr_valid` | in | 1 | request valid |
| `cpu_req_wr_ready` | out | 1 | request accepted |
| `cpu_req_wr_data` | in | `CPU_REQ_W` | packed {`addr`, `we`, `be`, `wdata`} |

Response stream (amber → CPU, slave output):

| Signal | Direction | Width | Payload |
|---|---|---|---|
| `cpu_rsp_rd_valid` | out | 1 | response valid |
| `cpu_rsp_rd_ready` | in | 1 | response accepted |
| `cpu_rsp_rd_data` | out | `CPU_RSP_W` | packed {`rdata`} |

: Table 4.0: CPU-side GAXI slave channels

Field packing follows the house field-width convention the AMBA wrappers use
(`CPU_REQ_W = ADDR_WIDTH + 1 + BUS_WIDTH/8 + BUS_WIDTH`, `CPU_RSP_W =
BUS_WIDTH`; the frontend's field config fixes the bit ranges). If the CPU
agent prefers named fields at the boundary, the flattened per-field view
(`fub_*`-style, the way the AMBA wrappers expose their FUB side) carries the
same payload — the packed GAXI streams are the contract; naming is RTL
bring-up detail.

The frontend latches the accepted request and holds it until `amber_control`
returns the response. Because the cache is blocking, the response stream is
naturally in-order and carries no ID tags. Write-allocate fills are
read-modify-write sequences inside `amber_control`; the GAXI slave itself
sees only single-beat reads and writes.

## No register block

amber is a parameter-only IP. There is no APB CSR or register block. All visibility — configuration, event counting, and debug — comes through the MonBus observation fabric (`amber_monlite`). This is a deliberate decision, not an omission, and it keeps the CPU-side port the only software-visible surface.
