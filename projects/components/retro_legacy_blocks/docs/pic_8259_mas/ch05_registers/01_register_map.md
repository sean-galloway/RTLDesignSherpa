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

# APB PIC 8259 - Register Map

Unlike the original Intel 8259A, this block does **not** use the legacy two-port
A0-based interface. It exposes a fully-decoded, 32-bit-aligned APB register file.
Each ICW/OCW and every status register has its own dedicated offset; there is no
A0 pin and no OCW3 read-select multiplexing. Only `regblk_addr[5:0]` is decoded,
so the map repeats every 0x40 within the 4 KB APB window, and unmapped offsets
(e.g. 0x2C) complete without `PSLVERR`.

## Register Map

| Offset | Register | Access | Reset | Description |
|--------|----------|--------|-------|-------------|
| 0x00 | PIC_CONFIG | RW | 0x0000_0004 | Global configuration and control (gates all operation) |
| 0x04 | PIC_ICW1 | WO | — | Initialization Command Word 1 (edge/level, single, ICW4-needed) |
| 0x08 | PIC_ICW2 | WO | — | Initialization Command Word 2 (interrupt vector base) |
| 0x0C | PIC_ICW3 | WO | — | Initialization Command Word 3 (cascade config; stored but inert) |
| 0x10 | PIC_ICW4 | WO | — | Initialization Command Word 4 (mode bits) |
| 0x14 | PIC_OCW1 | RW | 0x0000_00FF | Operation Command Word 1 - Interrupt Mask Register (IMR) |
| 0x18 | PIC_OCW2 | WO | — | Operation Command Word 2 (EOI / priority command) |
| 0x1C | PIC_OCW3 | WO | — | Operation Command Word 3 (special mask, read-select, poll) |
| 0x20 | PIC_IRR | RO | 0x0000_0000 | Interrupt Request Register |
| 0x24 | PIC_ISR | RO | 0x0000_0000 | In-Service Register |
| 0x28 | PIC_STATUS | RO | — | Initialization state and diagnostics |

**Access notes:** PIC_ICW1-ICW4, PIC_OCW2, and PIC_OCW3 are write-only in the
RTL - their read-back paths are tied to zero, so reading these offsets returns
0x0000_0000. Only PIC_CONFIG, PIC_OCW1 (IMR), PIC_IRR, PIC_ISR, and PIC_STATUS
return meaningful data on a read.

---

## Global Configuration

### PIC_CONFIG (Offset 0x00, RW)

The PIC is disabled out of reset. Firmware **must** set `pic_enable` before any
interrupt request can propagate - while `pic_enable=0` the core holds IRR at 0
and forces `int_out` low.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 0 | pic_enable | RW | 0 | Master enable (0=disabled, 1=enabled) |
| 1 | init_mode | RW | 0 | Initialization mode (0=operational, 1=init sequence) |
| 2 | auto_reset_init | RW | 1 | Automatically clear init_mode after ICW4 is written |
| 31:3 | Reserved | RO | 0 | Reserved |

---

## Initialization Command Words (ICW)

All ICW registers are write-only; reading them returns 0.

### PIC_ICW1 (Offset 0x04, WO)

| Bit | Name | Reset | Description |
|-----|------|-------|-------------|
| 0 | IC4 | 0 | 1 = ICW4 needed, 0 = ICW4 not needed |
| 1 | SNGL | 0 | 1 = single mode (no cascade), 0 = cascade mode |
| 2 | ADI | 0 | Call address interval (8080/8085 mode only) |
| 3 | LTIM | 0 | 1 = level triggered, 0 = edge triggered |
| 4 | ICW1 Marker | 1 | Always 1 to identify ICW1 (8259A compatibility) |
| 31:5 | Reserved | 0 | Reserved (the RTL implements no bits above bit 4) |

Note: the RTL stores only bits [4:0]. The legacy A7-A5 vector bits of an MCS-80
8259A are not implemented here.

### PIC_ICW2 (Offset 0x08, WO)

| Bits | Name | Reset | Description |
|------|------|-------|-------------|
| 7:0 | vector_base | 0x00 | Interrupt vector base. The delivered vector is `{vector_base[7:3], irq[2:0]}` |
| 31:8 | Reserved | 0 | Reserved |

### PIC_ICW3 (Offset 0x0C, WO)

Cascade configuration. See the implementation note below - this register is
stored but has no functional effect in the current RTL.

**Master mode:**
| Bits | Description |
|------|-------------|
| 7:0 | Bitmap of IR lines that have a slave attached (1 = slave present) |

**Slave mode:**
| Bits | Description |
|------|-------------|
| 2:0 | Slave ID (cascade input number 0-7) |

### PIC_ICW4 (Offset 0x10, WO)

| Bit | Name | Reset | Description |
|-----|------|-------|-------------|
| 0 | uPM | 1 | 1 = 8086/8088 mode, 0 = 8080/8085 mode |
| 1 | AEOI | 0 | Automatic EOI mode (see implementation note) |
| 3:2 | BUF (M/S) | 00 | Buffered-mode select: 00=non-buffered, 10=buffered slave, 11=buffered master |
| 4 | SFNM | 0 | Special fully nested mode (see implementation note) |
| 31:5 | Reserved | 0 | Reserved |

---

## Operation Command Words (OCW)

### PIC_OCW1 - Interrupt Mask Register (Offset 0x14, RW)

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 7:0 | imr | RW | 0xFF | Interrupt mask for IRQ0-7: 1 = masked (disabled), 0 = unmasked (enabled) |
| 31:8 | Reserved | RO | 0 | Reserved |

Reset masks all eight interrupts.

### PIC_OCW2 (Offset 0x18, WO)

| Bits | Name | Reset | Description |
|------|------|-------|-------------|
| 2:0 | irq_level (L2-L0) | 0 | IRQ level for specific EOI or set-priority |
| 4:3 | Reserved | 0 | Reserved (OCW2 identifier field in a legacy 8259A) |
| 7:5 | eoi_cmd (R,SL,EOI) | 0 | EOI / rotation command (see table) |
| 31:8 | Reserved | 0 | Reserved |

**EOI / rotation command encodings** (bits [7:5] = R, SL, EOI), as decoded by the RTL:

| R | SL | EOI | Command |
|---|----|-----|---------|
| 0 | 0 | 0 | Rotate on auto EOI (clear) |
| 0 | 0 | 1 | Non-specific EOI |
| 0 | 1 | 1 | Specific EOI (clears the IR selected by L2-L0) |
| 1 | 0 | 0 | Rotate on auto EOI (set) |
| 1 | 0 | 1 | Rotate on non-specific EOI |
| 1 | 1 | 0 | Set priority (L2-L0 becomes lowest priority) |
| 1 | 1 | 1 | Rotate on specific EOI |

### PIC_OCW3 (Offset 0x1C, WO)

| Bits | Name | Reset | Description |
|------|------|-------|-------------|
| 1:0 | read_reg_cmd (RIS,RR) | 00 | Read-register select: 00=no action, 10=read IRR, 11=read ISR (see implementation note) |
| 2 | P | 0 | Poll command (see implementation note) |
| 4:3 | OCW3 Marker | 01 | Always 01 to identify OCW3 |
| 6:5 | ESMM,SMM | 00 | Special mask mode: 10=reset special mask, 11=set special mask |
| 31:7 | Reserved | 0 | Reserved |

---

## Status / Readback Registers

### PIC_IRR - Interrupt Request Register (Offset 0x20, RO)

| Bits | Name | Reset | Description |
|------|------|-------|-------------|
| 7:0 | irr | 0 | Pending interrupt requests for IRQ0-7 (1 = request pending) |
| 31:8 | Reserved | 0 | Reserved |

IRR reflects requests before masking. In level mode the bits follow the IRQ
pins; in edge mode they are set on a rising edge. See the implementation note
below regarding clearing edge-triggered requests.

### PIC_ISR - In-Service Register (Offset 0x24, RO)

| Bits | Name | Reset | Description |
|------|------|-------|-------------|
| 7:0 | isr | 0 | In-service bits for IRQ0-7 (1 = interrupt being serviced) |
| 31:8 | Reserved | 0 | Reserved |

See the implementation note below - in the current RTL no path ever sets an
ISR bit, so this register reads 0x00.

### PIC_STATUS (Offset 0x28, RO)

Initialization-state and diagnostic readback. This register is the only way to
observe the init sequence progress from software.

| Bits | Name | Reset | Description |
|------|------|-------|-------------|
| 0 | init_complete | - | 1 = initialization complete, 0 = in init sequence |
| 3:1 | icw_step | - | Current ICW step (0 = not initialized, 4 = complete) |
| 4 | int_output | - | Current state of the INT output pin |
| 7:5 | highest_priority | - | Currently highest-priority IRQ (0-7) |
| 31:8 | Reserved | 0 | Reserved |

---

## Implementation Notes (RTL vs. classic 8259A)

The register file above matches the RTL exactly. Several classic-8259A
behaviors implied by the register names are **not** implemented in the current
core; they are documented here so firmware does not rely on them:

- **No INTA handshake / vector output.** The block has no `inta_n`, `cas[2:0]`,
  or `sp_n/en_n` pins - only `irq_in[7:0]` and `int_out`. The core computes an
  interrupt vector internally but leaves it on an unconnected wire reserved for
  future INTA support; no register exposes it to software.
- **ISR is never set (0x24 reads 0).** No acknowledge path sets an in-service
  bit, so PIC_ISR always reads 0x00. As a consequence, all PIC_OCW2 EOI
  variants, ISR-based interrupt nesting/blocking, and special mask mode have no
  effect on live state.
- **Edge-triggered IRR has no clear-on-acknowledge path.** In edge mode an IRR
  bit, once set, is only cleared by reset, an ICW1 write (re-initialization), or
  clearing `pic_enable`. Because EOI only touches the (always-zero) ISR, a
  pending edge interrupt can otherwise be removed only by masking it in the IMR.
  Level mode works normally because IRR follows the pin.
- **OCW3 read-select and poll are inert.** IRR and ISR are dedicated read-only
  registers at 0x20/0x24; the OCW3 `read_reg_cmd`/poll fields are decoded but
  not used, so the dedicated addresses make the read-select mechanism
  unnecessary.
- **Cascade, SFNM, buffered mode, and Auto EOI are stored but non-functional.**
  ICW3 (cascade), ICW4 SFNM/BUF, and ICW4 AEOI are captured in registers but
  have no functional effect in the current core (AEOI performs no
  end-of-interrupt because ISR is never set).

---

**Back to:** [PIC 8259 Specification Index](../pic_8259_mas_index.md)
