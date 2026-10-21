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

# Programmer-Visible Machine State

## The State an Integrator Programs Against

The architectural state visible to software is exactly:

| State element | Width | Reset value | Description |
|---------------|-------|-------------|-------------|
| PC | 32 | `RESET_ADDR` (parameter, default `32'h0000_0000`) | Program counter; fetch address of the currently retiring instruction |
| x0 | 32 | 0 | Hard-wired zero; reads return 0, writes are discarded in the register file |
| x1-x31 | 32 each | none (undefined) | General-purpose registers; the file has no reset (2026-10-20) and holds whatever it held until written |
| Memory | integrator-defined | integrator-defined | Flat byte-addressed space via the data port; the core provides no protection, mapping, or ordering semantics |
| Halt state | 1 + 4 | `halt=0`, cause `0x0` | Stop flag and cause code on the boundary (below) |

: Programmer-visible machine state

There are no CSRs, no counters, no privilege state, and no trap state. `mepc`, `mtvec`, `mstatus` and friends do not exist; the CSR instruction class retires through a stub (Chapter 3) whose only architectural effect is writing zero to rd.

## Consequences for Software

- **Program termination is a halt.** Programs end with ECALL (cause `0x1`); the harness reads the verdict from x3 (`gp`, the register the riscv-tests p-environment uses) at the final writeback before the halt.
- **The first fetch is `RESET_ADDR`.** Images must be linked so execution begins there; the loader integration must set the core's `RESET_ADDR` parameter to the image link base.
- **Software initializes every register it reads.** The register file has no reset (it maps to distributed RAM instead of 1,024 flops): after power-up a register is undefined, and after a reload it still holds the previous program's value. The riscv-tests p-env zeroes every register at its reset vector (`INIT_XREG`); kestrel's DV fails any test program that reads a register it never wrote.
- **Memory needs no setup.** There is no TLB, no cache to enable, no memory attributes: an address is data memory, full stop.

## The Halt Boundary as State

`halt` and `halt_cause[3:0]` are outputs, but software-visible behavior makes them part of the machine state: when any halt condition occurs, the PC freezes, writeback is suppressed, and retirement stops after one final trap beat on RVFI. The four causes:

| Cause | Name | Raised by | Spec counterpart (unpriv) |
|-------|------|-----------|---------------------------|
| `4'h1` | ECALL | decode, ECALL | environment-call exception |
| `4'h2` | EBREAK | decode, EBREAK | breakpoint exception |
| `4'h3` | IALIGN | core, taken branch/JAL/JALR to a non-4-aligned target | instruction-address-misaligned exception |
| `4'h4` | LALIGN | core, load whose address is not naturally aligned | load-address-misaligned exception |
| `4'h5` | SALIGN | core, store whose address is not naturally aligned | store-address-misaligned exception |
| `4'hF` | ILL | decode, illegal encoding | illegal-instruction exception |

: Halt causes (encodings centralized in `rtl/includes/kestrel_pkg.sv`)

The full halt timing contract — trap beat, post-hold sampling, and the absence of trap recovery — is specified in Chapter 4.

---

**Last Updated:** 2026-10-07
