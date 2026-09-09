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

# pic_8259 -- Overview

## Overview

The pic_8259 is an 8259A-compatible Programmable Interrupt Controller with an
APB interface. It handles interrupt management for legacy PC-compatible
systems: eight request lines in, one interrupt line out, with masking,
priority resolution, and an initialization sequence in between.

Implemented in the current RTL:

- 8 interrupt inputs (`irq_in[7:0]`) with a single `int_out` line.
  `irq_in` is sampled with NO synchronizer stages -- inputs are assumed
  synchronous to the core clock; asynchronous sources need external
  synchronization
- Fully-decoded 32-bit APB register file (no legacy A0 two-port model)
- Programmable priority with rotation (set-priority / rotate-on-EOI)
- Edge or level triggering
- Interrupt masking (IMR / OCW1)

Now the other half of the story. Register bits exist but are **not**
functional in the current core (see the register map implementation notes):

- Master/Slave cascade (ICW3)
- Polling mode (OCW3)
- Special fully nested mode (ICW4 SFNM)
- Buffered mode (ICW4 BUF)

Automatic EOI (ICW4 AEOI) performs no end-of-interrupt but is NOT inert:
it arms a defective rotation path (with OCW2 0x80 the priority base rotates
every clock while int_out is asserted -- see Chapter 5 and issue #50). There
is also no INTA handshake or vector-output pin.

### Applications

- PC-compatible interrupt management
- Legacy device support
- x86 system integration

## Functional Description

### Figure 1.1: PIC 8259 Block Diagram

![PIC 8259 Block Diagram](../assets/svg/pic_8259_top.png)

### Register Summary

The block uses a fully-decoded 32-bit register file, not the legacy A0 two-port
model. See [Chapter 5: Register Map](../ch05_registers/01_register_map.md) for
full field definitions.

| Offset | Register | Access | Description |
|--------|----------|--------|-------------|
| 0x00 | PIC_CONFIG | RW | Global configuration (pic_enable, init_mode, auto_reset_init) |
| 0x04 | PIC_ICW1 | WO | Initialization Command Word 1 |
| 0x08 | PIC_ICW2 | WO | Initialization Command Word 2 (vector base) |
| 0x0C | PIC_ICW3 | WO | Initialization Command Word 3 (cascade; inert) |
| 0x10 | PIC_ICW4 | WO | Initialization Command Word 4 |
| 0x14 | PIC_OCW1 | RW | Interrupt Mask Register (IMR) |
| 0x18 | PIC_OCW2 | WO | EOI / priority command |
| 0x1C | PIC_OCW3 | WO | Special mask / read-select / poll |
| 0x20 | PIC_IRR | RO | Interrupt Request Register |
| 0x24 | PIC_ISR | RO | In-Service Register |
| 0x28 | PIC_STATUS | RO | Initialization state / diagnostics |

The PIC is disabled at reset - firmware must BOTH complete the ICW
initialization sequence (ICW1 -> ICW2 -> ICW3 if cascaded -> ICW4 if
requested; PIC_STATUS.init_complete=1) AND set `pic_enable` (PIC_CONFIG
bit 0) before any interrupt can be requested or delivered -- out of reset
the init FSM sits in INIT_IDLE and IRR never updates.

### Interrupt Priority

| IRQ | Default Priority |
|-----|-----------------|
| IR0 | Highest (0) |
| IR1 | 1 |
| IR2 | 2 (cascade input in a classic master; cascade not implemented here) |
| IR3 | 3 |
| IR4 | 4 |
| IR5 | 5 |
| IR6 | 6 |
| IR7 | Lowest (7) |

### Priority Modes

- **Fixed Priority**: IR0 highest, IR7 lowest
- **Rotating Priority**: Lowest priority rotates after EOI
- **Specific Priority**: Programmable lowest priority

## Waveforms

### Waveform 1.1: Interrupt Request

Shows an IRQ input assertion triggering the interrupt process.

![PIC Interrupt Request](../assets/wavedrom/timing/pic_interrupt_request.png)

When an IR pin asserts, the corresponding IRR bit is set. The priority resolver selects the highest priority unmasked interrupt and asserts INT to the CPU.

### Waveform 1.2: Interrupt Acknowledge Sequence

The two-pulse INTA sequence from CPU to PIC.

![PIC Interrupt Acknowledge](../assets/wavedrom/timing/pic_interrupt_acknowledge.png)

On the first INTA pulse, priority is frozen and IRR transfers to ISR. On the second INTA pulse, the PIC outputs the interrupt vector (base + IR number) on the data bus.

> Note: the current RTL implements no INTA handshake. There are no `inta_n`,
> `cas`, or `sp_n/en_n` pins, ISR is never set, and the computed vector is not
> exposed to software. This waveform describes classic-8259A behavior that this
> block does not yet provide.

### Waveform 1.3: End-of-Interrupt (EOI)

Software clears the in-service bit with an EOI command.

![PIC EOI](../assets/wavedrom/timing/pic_eoi.png)

Non-specific EOI (0x20) clears the highest priority ISR bit. Specific EOI (0x60-0x67) clears a designated IR.

> Note: because the current RTL never sets an ISR bit, the ISR-CLEARING half
> of EOI is inert -- but the ROTATION side effects are live: rotate-on-
> specific-EOI (0xE0-0xE7) moves the priority base exactly like set-priority,
> and rotate-on-non-specific-EOI (0xA0) sets the base to the highest
> in-service IRQ, which is always IRQ0 because ISR is never set. Classic
> 8259 code issuing 0xA0 silently scrambles arbitration. See the register
> map implementation notes.

### Waveform 1.4: Cascade Mode

Master-slave configuration for 15 IRQ sources.

![PIC Cascade](../assets/wavedrom/timing/pic_cascade.png)

Slave INT connects to master IR2. During INTA, master outputs cascade select (CAS) lines. Slave with matching ID provides the interrupt vector.

> Note: cascade mode is not implemented in the current RTL. ICW3 is stored but
> inert, and there are no CAS or SP/EN pins. This waveform is illustrative of the
> classic-8259A architecture only.

### Waveform 1.5: Priority Rotation

Automatic priority rotation for equal-service scheduling.

![PIC Priority Rotation](../assets/wavedrom/timing/pic_priority_rotation.png)

Rotate-on-EOI (0xA0) makes the just-serviced IR the lowest priority, implementing round-robin scheduling among interrupt sources.

> Note: set-priority (0xC0-0xC7) and rotate-on-specific-EOI (0xE0-0xE7)
> both move the priority base in the current RTL (the latter ignores the
> inert ISR-clear half). Rotate-on-non-specific-EOI (0xA0) always rotates
> the base to 0 because ISR is never set -- NOT round-robin. See the
> register map implementation notes.

## Navigation

**Next:** 02_architecture.md *(planned, not yet written)*
