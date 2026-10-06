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

`amber_cpu_frontend` presents a GAXI request/response slave. Signal names are
the amber GAXI binding proposed by this specification; the frontend RTL may
adopt the packed field-config vectors the house GAXI primitives use
internally — the channel semantics in this table are the contract.

| Signal | Direction | Width | Meaning |
|---|---|---|---|
| `gaxi_addr` | in | `ADDR_WIDTH` | byte address of the access |
| `gaxi_wdata` | in | `BUS_WIDTH` | write data (single beat) |
| `gaxi_we` | in | 1 | 1 = write, 0 = read |
| `gaxi_be` | in | `BUS_WIDTH/8` | byte enables for writes |
| `gaxi_valid` | in | 1 | request valid |
| `gaxi_ready` | out | 1 | request accepted |
| `gaxi_rdata` | out | `BUS_WIDTH` | read response data |
| `gaxi_rvalid` | out | 1 | response valid |
| `gaxi_rready` | in | 1 | response accepted |

: Table 4.0: CPU-side GAXI slave port

The frontend latches the accepted request and holds it until `amber_control` returns the response. Because the cache is blocking, the response channel is naturally in-order and carries no ID tags. Write-allocate fills are expressed as read-modify-write sequences inside `amber_control`; the GAXI slave itself sees only single-beat reads and writes.

## No register block

amber is a parameter-only IP. There is no APB CSR or register block. All visibility — configuration, event counting, and debug — comes through the MonBus observation fabric (`amber_monlite`). This is a deliberate decision, not an omission, and it keeps the CPU-side port the only software-visible surface.
