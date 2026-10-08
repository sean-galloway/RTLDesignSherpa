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

# Fabric-Side AXI4 Masters

## Where they live

The `amber` top uses the house `axi4_master_rd` and `axi4_master_wr` wrappers for plain AXI4 memory access. These masters are functionally AXI4; they carry no ACE fields and no snoop channels. Fill requests become AR bursts; dirty victim drains become AW/W/B bursts.

## Burst behavior

amber issues whole-line fills and whole-line drains. The burst length is `LINE_BYTES / (BUS_WIDTH/8)` beats. The address is aligned to the line size; `ARSIZE` and `AWSIZE` are derived from `BUS_WIDTH`; `ARBURST`/`AWBURST` are `INCR`. Single-outstanding operation means there is one AR transaction and one AW transaction in flight at any time, so no reorder buffer is needed.

## Port summary

The plain AXI4 master stack exposes the standard five AXI4 channels toward memory:

| Channel | Direction from amber | Purpose |
|---|---|---|
| AR | out | read address for fill |
| R | in | read data for fill |
| AW | out | write address for dirty victim drain |
| W | out | write data for dirty victim drain |
| B | in | write response for dirty victim drain |

: Table 4.1: Plain AXI4 channels in the pair rig

The exact pin names and widths follow the `axi4_master_rd` and `axi4_master_wr` module parameters. The cache supplies address, length, size, and burst type; ID and user fields pass through or are tied to defaults configurable at the top.

## D3: decided

The memory-side interface is PRD **D3, decided 2026-10-07 (v0.6)**: AXI4
read/write masters on the house `axi4_master_rd`/`axi4_master_wr` wrappers
(the stream/rapids pattern), observed through `*_monlite` per D8 — chosen
over GAXI (D2 already spent that on the CPU side) and over a simple SRAM
bring-up port. The fill/drain engines drive the `fub_axi_*` upstream side
of those wrappers; ID/user fields take the wrappers' parameter defaults;
skid depths are the wrappers' house defaults. The pair rig's shared memory
hangs off the `m_axi_*` sides through house fabric (Chapter 6).
