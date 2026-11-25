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

## Implemented Extensions

| Extension | Instructions | Notes |
|-----------|--------------|-------|
| RV32I | The 37 computational, control-transfer and load/store instructions, `fence`, `ecall`, `ebreak` | `fence` retires as a no-op: the caches are blocking and one access is in flight at a time |
| M | `mul`, `mulh`, `mulhsu`, `mulhu`, `div`, `divu`, `rem`, `remu` | One iterative unit; the instruction holds in EX until done (costs: "Performance Characteristics") |
| Zicsr | `csrrw`, `csrrs`, `csrrc`, `csrrwi`, `csrrsi`, `csrrci` | The machine-mode CSRs listed in "Programmer-Visible Machine State and Traps"; any other address is an illegal instruction |
| Zifencei | `fence.i` | Cleans the D\$, invalidates the I\$ and refetches the next instruction (cacheless: refetch only) |
| Privileged (M-mode) | `mret`, `wfi` | `wfi` retires as a no-op |

: Implemented ISA

`misa` reads `0x4000_1100`: MXL = 1 (32-bit), I and M. The core decodes through the shared `rv32i_decode` with `M_EXT=1` and `ZICSR=1` (PRD P11).

## Division Edge Cases

The M results follow the unprivileged specification's division table, which spike agrees with:

| Case | `div` / `divu` | `rem` / `remu` |
|------|----------------|----------------|
| Divisor 0 | all ones (-1 / 2^32 - 1) | the dividend |
| `div`: -2^31 / -1 (overflow) | -2^31 | 0 |

: Division by zero and overflow results

Both cases take the unit's early-out path (1 stall cycle instead of 33).

## Alignment

IALIGN is 32: there is no C extension. A taken branch, JAL or JALR whose target is not word-aligned traps with an instruction-address-misaligned exception. Loads and stores must be naturally aligned; a misaligned halfword or word access traps (load or store address misaligned) and performs no memory access. The riscv-tests `ma_data` test, which expects misaligned accesses to complete, is therefore an expected failure, the same as on spike.

## Not Implemented

| Feature | Reason |
|---------|--------|
| Supervisor and user modes, MMU | PRD §2: machine mode only |
| PMP regions | PRD P6: the PMP CSRs exist with zero entries (read 0, writes ignored) |
| Zicntr (`cycle`, `time`, `instret`) | PRD P6: no counters; cycle counts come from the TB and RVFI |
| Debug mode and triggers | Not in scope |
| Access-fault exceptions | Not built; see "System Overview" |
| A, F, C, D | Later rungs (gyrfalcon-A, garuda) |

: Features outside peregrine

---

**Last Updated:** 2026-11-25
