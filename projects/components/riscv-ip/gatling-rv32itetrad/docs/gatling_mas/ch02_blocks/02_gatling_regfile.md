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


# gatling_regfile

## Purpose

The four context register files as one 128-entry array indexed `{context, register}`, with two registered read ports and one write port, in block RAM.

## Interface

| Port | Dir | Description |
|---|---|---|
| `rs_ctx`, `rs1_addr`, `rs2_addr` | in | Read address (D stage) |
| `rs1_data`, `rs2_data` | out | Read data, one cycle later (X stage) |
| `rd_ctx`, `rd_addr`, `rd_data`, `rd_wen` | in | Write (W stage) |

: Table 2.3: gatling_regfile ports

## Structure

Two copies of the array (`regs_a`, `regs_b`), each written on every write, give two read ports over one write port; each maps to one block RAM. The read is registered, which is the latency the barrel already has between D and X, so block RAM costs no cycle.

x0 reads zero through a read-side mask: `rs*_zero_q` registers whether the address was x0 and zeroes the RAM output. kestrel instead writes x0 to zero in reset; with four contexts that would be four reset writes, and the mask also makes a never-written RAM read zero for x0 in formal, where the array starts unconstrained.

The array has no reset (SRAM rule). D and W always hold different contexts, so the barrel never reads and writes the same entry in one cycle.
