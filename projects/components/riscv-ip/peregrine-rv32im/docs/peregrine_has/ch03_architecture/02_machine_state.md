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

# Programmer-Visible Machine State and Traps

## Registers

The 32 general-purpose registers (x0 reads zero) and the PC. The PC resets to the `RESET_ADDR` parameter. The register file has no reset; x0 is kept zero by writes during reset.

## Machine-Mode CSRs

| Address | CSR | Access | Contents |
|---------|-----|--------|----------|
| 0x300 | `mstatus` | RW | MIE (bit 3), MPIE (bit 7); MPP (bits 12:11) reads 11 (machine mode); other bits read 0 |
| 0x301 | `misa` | RO (writes ignored) | `0x4000_1100` (RV32IM) |
| 0x304 | `mie` | RW | MSIE (3), MTIE (7), MEIE (11); other bits read 0 |
| 0x305 | `mtvec` | RW | Trap vector, direct mode only: bits 1:0 read 0 |
| 0x310 | `mstatush` | RO (writes ignored) | 0 |
| 0x340 | `mscratch` | RW | 32 bits |
| 0x341 | `mepc` | RW | Bits 1:0 read 0 (IALIGN = 32) |
| 0x342 | `mcause` | RW | Interrupt bit 31 and the code |
| 0x343 | `mtval` | RW | Trap value (see Exceptions below) |
| 0x344 | `mip` | RO (writes ignored) | MSIP, MTIP, MEIP from the interrupt pins |
| 0x3A0-0x3AF | `pmpcfg0-15` | RO (writes ignored) | 0: zero PMP entries |
| 0x3B0-0x3EF | `pmpaddr0-63` | RO (writes ignored) | 0 |
| 0xF11-0xF15 | `mvendorid`, `marchid`, `mimpid`, `mhartid`, `mconfigptr` | RO | 0 |

: Implemented CSRs

An access to any other address, or a write to a read-only address (bits 11:10 = 11), is an illegal-instruction exception. `csrrs` and `csrrc` with `rs1 = x0` (and their immediate forms with `zimm = 0`) do not write, so they may read a read-only CSR. A write to `misa`, `mstatush`, `mip` or a PMP CSR is accepted and ignored (WARL).

## Exceptions

| Exception | mcause | mtval | Raised in |
|-----------|--------|-------|-----------|
| Instruction address misaligned | 0 | The misaligned target | EX (taken branch, JAL, JALR) |
| Illegal instruction | 2 | The instruction word | ID (decode) or EX (missing or read-only CSR) |
| Breakpoint (`ebreak`) | 3 | The PC | ID |
| Load address misaligned | 4 | The address | EX |
| Store address misaligned | 6 | The address | EX |
| Environment call from M-mode (`ecall`) | 11 | 0 | ID |

: Exceptions, causes and trap values

An instruction raises at most one exception. Decode's (illegal, `ecall`, `ebreak`) takes precedence over a CSR illegal, then a misaligned target, then a misaligned access.

## Interrupts

| Interrupt | mcause | Source in `peregrine_top` | Priority |
|-----------|--------|---------------------------|----------|
| Machine external (MEI) | 0x8000_000B | `irq_external` pin | Highest |
| Machine software (MSI) | 0x8000_0003 | CLINT `msip` | Middle |
| Machine timer (MTI) | 0x8000_0007 | CLINT `mtime >= mtimecmp` | Lowest |

: Interrupts

An interrupt is taken when it is pending in `mip`, enabled in `mie`, and `mstatus.MIE` is set. The inputs are levels: software clears the source (writes `msip`, moves `mtimecmp`, services the external device).

## Trap Entry and Return

On a trap, in one cycle: `mepc` takes the trapping instruction's PC (for an interrupt, the PC of the instruction that did not execute), `mcause` and `mtval` take the values above, `mstatus.MPIE` takes `MIE` and `MIE` clears, and the next instruction is fetched from `mtvec`. `mret` restores `MIE` from `MPIE`, sets `MPIE`, and resumes at `mepc`.

Traps are precise: every older instruction has completed and no younger instruction has written a register, memory or a CSR. "Trap and Interrupt Behavior" gives the boundary rules, including the one exception to "take the interrupt on the next instruction to reach MEM".

---

**Last Updated:** 2026-11-25
