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

# I/O Advanced Programmable Interrupt Controller (IOAPIC)

**Status:** Implemented - 37/37 in all six DV configurations (2026-09-09)
**Priority:** Medium
**Address:** `0x4000_6000 - 0x4000_6FFF` (4KB window)

---

## Overview

Intel 82093AA-compatible interrupt router: 24 IRQ inputs, a programmable
redirection table reached through the IOREGSEL/IOWIN indirect window, and a
single valid/ready delivery interface to the CPU/LAPIC.

## What is implemented

- 24 IRQ inputs, asynchronous, three-stage synchronized in `ioapic_core`
- Edge and level trigger modes, active-high/active-low polarity, per-pin mask
- Static-priority arbitration: lowest IRQ number wins
- One outstanding delivery on a valid/ready handshake - no delivery FSM
- Per-pin Remote IRR: a level interrupt blocks ITS OWN pin until EOI, other
  pins keep delivering, and a lost or wrong-vector EOI cannot stall the block
- EOI matched against the vector actually DELIVERED on that pin, so an RTE may
  be re-pointed between delivery and EOI
- IOREGSEL/IOWIN indirect access. Only APB `0x000` (IOREGSEL) and `0x004`
  (IOWIN) are software-visible in the 4 KB window; the indirect pair is the
  only path to the register file. Three classes of access never reach the
  register block:
  - an address above `0x0FF` - dropped, PSLVERR (it would otherwise alias onto
    the 8-bit register address modulo `0x100`)
  - an address inside `0x000-0x0FF` that is neither IOREGSEL nor IOWIN -
    dropped, PSLVERR. This was a backdoor: such an address used to reach the
    register block at its raw offset, so a direct write to `0x008` rewrote
    IOAPICID and one to `0x014` rewrote IOREDTBL[0].REDIR_LO
  - IOWIN with a selector the 82093AA does not implement - dropped, and NOT an
    error: the address is legal, the register is not, and the architectural
    answer is a read of zero
- CDC_ENABLE=1: the whole CPU/LAPIC-facing interface is presented in pclk and
  crosses into ioapic_clk through matched-latency synchronizers

## Destination mode

`irq_out_dest_mode` carries the RTE's destination mode alongside
`irq_out_dest`: 0 means the destination is a physical APIC ID, 1 means it is a
logical bitmask. An IOAPIC does not decode logical destinations itself - it
forwards the field and the mode, and the local APICs do the matching - so
forwarding the mode is the whole of this block's responsibility for logical
delivery (RLB-008). Delivery modes other than Fixed are likewise forwarded on
`irq_out_deliv_mode` unmodified.

## Not implemented (see vault/Tasks/RLB/open.md, RLB-008)

LowestPriority arbitration, which needs processor priority tracking this block
has no interface for; dynamic priority rotation (arbitration is static, lowest
IRQ number wins); multi-IOAPIC routing; boot-interrupt delivery; MSI/MSI-X.

## Files

| File | Role |
|---|---|
| `apb4_ioapic.sv` | Top level: APB slave (CDC or not), LAPIC interface crossing |
| `ioapic_core.sv` | Synchronization, edge/level tracking, arbitration, Remote IRR |
| `ioapic_config_regs.sv` | IOREGSEL/IOWIN translation, PeakRDL wrapper, hwif mapping |
| `ioapic_regs.sv`, `ioapic_regs_pkg.sv` | PeakRDL generated - regenerate only via `bin/peakrdl_generate.py` |
| `peakrdl/ioapic_regs.rdl` | Register source of truth (fixed at 24 entries) |
| `filelists/apb4_ioapic.f` | Compile closure |

## Verification

`projects/components/retro_legacy_blocks/dv/tests/test_apb4_ioapic.py`, six
configurations (CDC off/on x gate/func/full). The defect-regression suite for
GitHub issue #48 is `dv/tbclasses/ioapic/ioapic_tests_medium.py`.

```bash
cd projects/components/retro_legacy_blocks/dv/tests
make clean-all && make run-apb4_ioapic-full
```

## Specification

`projects/components/retro_legacy_blocks/docs/ioapic_mas/`

---

**Last Updated:** 2026-09-09
