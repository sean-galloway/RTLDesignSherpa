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
- Arbitration in two policies: static priority (lowest IRQ number wins, the
  82093AA scheme and the reset default) or round robin behind
  `IOAPICARBCFG.rr_enable`
- One outstanding delivery on a valid/ready handshake - no delivery FSM - with
  `irq_out_retry` on the same handshake, so a receiver that could not place
  the interrupt gets it offered again instead of losing it
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

## LowestPriority is delegated, and that is not a dodge

An IOAPIC does not track CPU priority, and never did. On the APIC bus it
broadcast the message and the local APICs arbitrated among themselves using
their Arbitration Priority Registers -- roughly the maximum of a CPU's task
priority class, its highest in-service vector and its highest pending one --
and whichever was lowest accepted. The IOAPIC only had to know whether anybody
took it.

That is why the destination, the destination mode and the delivery mode are
forwarded unmodified. The half this block was missing was never the choosing.
It was being told the choice FAILED.

`irq_out_retry` is that half:

| handshake | meaning | what the block does |
|-----------|---------|---------------------|
| `ready` low | the receiver is not ready | nothing; the offer stands, the rotation does not move |
| `ready`, `retry` low | a CPU accepted | retire the edge latch, set Remote IRR, latch the delivered vector, move the rotation |
| `ready`, `retry` high | consumed, nobody could accept | move the rotation and OFFER IT AGAIN -- nothing retires |

Tie `irq_out_retry` low and the channel behaves exactly as it did before this
existed: every completed handshake is an acceptance.

**What a consumer owes.** For delivery mode 001 the receiver gets the vector
and the destination set and must pick the lowest-priority CPU in it, or refuse
with retry when none can take it. None of that lives here, which is the point.

**One sharp edge, stated rather than hidden.** Under static priority a refused
pin is still the lowest eligible number, so it wins the next arbitration
immediately and a persistent refusal monopolises the channel. Round robin
fixes it, which is the same answer static priority's starvation has everywhere
else in this block.

**Why the channel is shaped this way.** The intent is to hang a CPU off it
across a bus. A payload plus a handshake plus a status bridges onto AMBA
readily -- the retry becomes a bus response. A bundle of live per-CPU priority
registers would not: it would be stale by the time it crossed, and the IOAPIC
would be choosing on numbers that had already moved.

## Arbitration is static unless you say otherwise

Static priority is the 82093AA scheme: scan up from pin 0, the lowest eligible
number wins. Its weakness is a consequence of the rule rather than a bug. A
level pin that becomes eligible again the cycle after software EOIs it holds
the low ground forever, and every pin above it starves.

Writing 1 to `IOAPICARBCFG.rr_enable` starts the scan just above the pin that
was last ACCEPTED, and wraps. The pin just served becomes the last one the scan
reaches, so every eligible pin is served before any pin is served twice.
Priority becomes a position in the rotation rather than an IRQ number.

The pointer moves only on an accept. A pick that the consumer never takes must
not move it, or a stalled consumer would walk the rotation round the ring
without delivering anything.

`IOAPICARBCFG` is NOT an 82093AA register. Selector `0x03` is reserved on the
part, and this block uses it for the one choice the datasheet's scheme cannot
express. A driver written for the 82093AA never writes it and gets static
priority.

## Destination mode

`irq_out_dest_mode` carries the RTE's destination mode alongside
`irq_out_dest`: 0 means the destination is a physical APIC ID, 1 means it is a
logical bitmask. An IOAPIC does not decode logical destinations itself - it
forwards the field and the mode, and the local APICs do the matching - so
forwarding the mode is the whole of this block's responsibility for logical
delivery (RLB-008). Delivery modes other than Fixed are likewise forwarded on
`irq_out_deliv_mode` unmodified.

## Not implemented (see vault/Tasks/RLB/open.md, RLB-008)

Multi-IOAPIC routing; boot-interrupt delivery; MSI/MSI-X.

LowestPriority is delegated rather than absent, and the other delivery modes
(SMI, NMI, INIT, ExtINT) are FORWARDED rather than acted on: they ride
`irq_out_deliv_mode` unmodified and it is the receiver that interprets them.
See "LowestPriority is delegated" above for what the block does and does not
owe in that arrangement.

## Files

| File | Role |
|---|---|
| `apb4_ioapic.sv` | Top level: APB slave (CDC or not), LAPIC interface crossing |
| `ioapic_core.sv` | Synchronization, edge/level tracking, arbitration, Remote IRR |
| `ioapic_config_regs.sv` | IOREGSEL/IOWIN translation, PeakRDL wrapper, hwif mapping |
| `ioapic_regs.sv`, `ioapic_regs_pkg.sv` | PeakRDL generated - regenerate only via `bin/peakrdl_generate.py` |
| `../../rdl/ioapic/ioapic_regs.rdl` | Register source of truth (fixed at 24 entries) |
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
