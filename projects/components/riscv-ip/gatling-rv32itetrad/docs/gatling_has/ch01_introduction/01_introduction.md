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


# Introduction

gatling is the per-tetrad compute engine of the tile (PRD 1): one RV32I processor with four hardware contexts, one per cell of the tetrad, sharing one datapath. The four contexts run four independent programs. Each context executes one instruction per four clocks; together they execute one per clock.

This first build is the RV32I barrel (owner, 2026-10-21). The Xcell extension -- the custom-0 instructions that move data between a context and its cell (PRD 3.1) -- is reserved and arrives with the cell seam. On the Nexys A7 the four contexts run the riscv-tests rv32ui battery at once, four different programs side by side.
