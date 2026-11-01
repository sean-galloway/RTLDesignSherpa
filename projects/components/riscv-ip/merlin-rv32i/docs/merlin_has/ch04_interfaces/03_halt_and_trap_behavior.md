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

# Halt and Trap Behavior

## Halt Causes

This section will enumerate the halt-cause encodings: ECALL, EBREAK, illegal instruction, instruction-address misaligned, load-address misaligned, and store-address misaligned.

## Halt Timing

This section will describe when halt is detected (in WB), how it latches `halt_q`, freezes the PC, and flushes younger in-flight instructions.

## RVFI Trap Beat

This section will explain that the halting instruction retires as the final RVFI beat with `rvfi_trap=1`.

---

**Last Updated:** 2026-11-01
