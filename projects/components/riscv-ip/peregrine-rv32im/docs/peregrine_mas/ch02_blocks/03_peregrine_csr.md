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

# peregrine_csr

**Module:** `peregrine_csr.sv`

## Responsibility

The machine-mode CSR file of PRD P6: one combinational read port (the CSR instruction in EX), one write port, and the trap-entry and `mret` updates, the three driven by the MEM-stage commit with at most one per cycle. It also makes the interrupt-pending decision the commit point samples. The register map is in the HAS ("Programmer-Visible Machine State and Traps").

## Parameters

<!-- GEN:params:peregrine_csr -->

| Parameter | Kind | Type | Default | Description |
|----------------|----------|------------|--------------|------------------------------|
| `M_EXT` | parameter | `bit` | `1'b0` | Sets misa.M |

: peregrine_csr parameters

<!-- /GEN -->

## Ports

<!-- GEN:ports:peregrine_csr -->

| Port | Dir | Width | Description |
|----------------------|----------|------------|----------------------------------|
| `clk` | input | `1` | Clock |
| `rst_n` | input | `1` | Reset |
| `raddr` | input | `[11:0]` | CSR address of the instruction in EX |
| `rdata` | output | `[31:0]` | Its current value |
| `r_exists` | output | `1` | The address is implemented (0: illegal instruction) |
| `wen` | input | `1` | CSR write committed in MEM |
| `waddr` | input | `[11:0]` | Its address |
| `wdata` | input | `[31:0]` | Its value |
| `trap_take` | input | `1` | Trap entry committed in MEM |
| `trap_cause` | input | `[31:0]` | mcause to write |
| `trap_epc` | input | `[31:0]` | mepc to write (the trapping PC) |
| `trap_tval` | input | `[31:0]` | mtval to write |
| `mret_take` | input | `1` | mret committed in MEM |
| `irq_software` | input | `1` | MSIP pin (level) |
| `irq_timer` | input | `1` | MTIP pin (level) |
| `irq_external` | input | `1` | MEIP pin (level) |
| `mtvec` | output | `[31:0]` | Trap vector (direct mode) |
| `mepc` | output | `[31:0]` | Return PC for mret |
| `irq_pending` | output | `1` | An enabled interrupt was pending and mstatus.MIE set in the previous cycle (registered) |
| `irq_cause` | output | `[31:0]` | Its mcause (MEI > MSI > MTI) |

: peregrine_csr ports

<!-- /GEN -->

## Behavior

- **Read.** `rdata` by `raddr`; `r_exists = 0` for an unimplemented address, which the core turns into an illegal-instruction exception. The PMP range 0x3A0-0x3EF exists and reads 0.
- **Update priority.** `trap_take`, then `mret_take`, then `wen`. They never coincide: each is the commit of the one instruction in MEM.
- **Trap entry:** `MPIE <= MIE`, `MIE <= 0`, `mepc <= trap_epc[31:2]`, `mcause <= trap_cause`, `mtval <= trap_tval`.
- **mret:** `MIE <= MPIE`, `MPIE <= 1`.
- **Write masks:** `mie` keeps only MSIE, MTIE, MEIE; `mtvec` and `mepc` keep bits 31:2; `mstatus` keeps MIE and MPIE; writes to `misa`, `mstatush`, `mip` and the PMP CSRs are ignored.
- **Interrupts.** The decision `|(mie & mip) & mstatus.MIE`, with `mip` taken from the three pins each cycle, is registered: `irq_pending` and `irq_cause` (MEI, then MSI, then MTI) are what the previous cycle saw (TASK-006; `mie` through the decision into amber's request accept was a 75 MHz critical path). A cycle with `wen`, `trap_take` or `mret_take` loads `irq_pending = 0`, so the cycle after a CSR write that disables interrupts, a trap entry (which clears MIE) or an `mret` never takes an interrupt on the old enables. An interrupt is recognized one cycle after its pin and enables allow it, and a pin that drops is still seen for one cycle.
- **Reset.** Every CSR resets to 0, so interrupts are disabled and `mtvec` is 0 until software sets them.

---

**Last Updated:** 2026-11-25
