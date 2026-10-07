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

# kestrel_regfile

## Purpose

`kestrel_regfile` is the 32 x 32-bit general-purpose register file: two combinational read ports, one synchronous write port, and the architectural x0 rule enforced in hardware. Reads are combinational because the single-cycle design cannot afford a read latency; the write commits on the clock edge.

## Interface

| Port | Direction | Width | Description |
|------|-----------|-------|-------------|
| `clk` / `rst_n` | Input | 1 / 1 | Clock; active-low reset clears all 32 entries |
| `rs1_addr` / `rs1_data` | Input / Output | 5 / 32 | Read port 1 (combinationally `regs[rs1_addr]`) |
| `rs2_addr` / `rs2_data` | Input / Output | 5 / 32 | Read port 2 |
| `rd_addr` / `rd_data` / `rd_wen` | Input / Input / Input | 5 / 32 / 1 | Write port; committed on the edge when `rd_wen` and `rd_addr != 0` |

: kestrel_regfile interface

## Internal Structure and Rules

- Storage is `logic [31:0] regs [32]`, reset to all zeros (so no register carries architectural garbage out of reset, and pre-load observability is deterministic).
- **The x0 rule lives here:** writes with `rd_addr == 0` are discarded by the write condition `rd_wen && (rd_addr != X0_ADDR)`; reads of x0 return the reset/stored zero naturally.
- The core additionally gates `rd_wen` (into `rd_wen_eff`) so that the retry's first beat and halted cycles never reach this port — see the kestrel_core chapter.
- No write-forwarding exists: a write commits on the edge and is readable the next cycle. This is exactly the single-cycle contract (a store is visible to the next cycle's load *through the memory*; a register write is visible to the next instruction *through the register file*).

---

**Last Updated:** 2026-10-07
