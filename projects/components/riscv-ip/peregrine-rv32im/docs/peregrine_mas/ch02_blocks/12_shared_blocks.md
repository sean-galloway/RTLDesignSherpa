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

# Shared Blocks

peregrine reuses these blocks unchanged; their documentation is with their owners.

| Block | Owner | Used as |
|-------|-------|---------|
| `rv32i_decode` | riscv-ip/common-rv32i | ID decode, with `M_EXT=1` and `ZICSR=1` (PRD P11): `m_op`, `csr_op` and `mret` outputs, trap causes in place of halt causes, `wfi` as a no-op |
| `rv32i_imm_gen` | riscv-ip/common-rv32i | ID immediate |
| `rv32i_alu` | riscv-ip/common-rv32i | EX ALU; its compare flags are left unconnected, as in kestrel and merlin, because the core compares branch operands on its own comparator |
| `rv32i_pkg` | riscv-ip/common-rv32i | ALU-op enum; the halt-cause encodings peregrine reuses as in-pipeline exception codes |
| `kestrel_regfile` | riscv-ip/kestrel-rv32i | 2 combinational reads, 1 write, no reset; x0 is kept zero by the core |
| `reset_sync` | rtl/cdc | Three-stage reset synchronizer at the core and wrapper boundary |
| `arbiter_round_robin` | rtl/common | Inside `peregrine_axi4_arb` |
| `amber_top` | cache-ip/amber-mesi-l1 | The D\$ inside `peregrine_top` |

: Blocks peregrine reuses

`rv32i_decode`'s `M_EXT` and `ZICSR` parameters default to 0, and its new outputs are constant 0 then, so kestrel, merlin and gatling elaborate the same logic as before (their suites and the common-rv32i unit tests were the proof, TASK-001 stage 1).

---

**Last Updated:** 2026-11-25
