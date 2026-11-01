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

# ISA Scope

## Implemented Instructions

This section will list the RV32I base integer instructions implemented by merlin, organized by opcode group (OP-IMM, OP, LUI, AUIPC, JAL, JALR, BRANCH, LOAD, STORE, SYSTEM/FENCE/ECALL/EBREAK).

## CSR-Stub Behavior

This section will explain that CSR instructions are not architecturally implemented; the core treats them as a stub that forces the writeback value to zero so the forwarding paths remain well-defined.

## Unimplemented Extensions

This section will state that M, A, F, D, C, Zicsr, and Zifencei are out of scope for this version.

---

**Last Updated:** 2026-11-01
