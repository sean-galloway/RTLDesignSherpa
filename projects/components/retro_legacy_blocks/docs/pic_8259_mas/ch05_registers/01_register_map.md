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

## Register Access

| Offset | A0 | Read | Write |
|--------|-----|------|-------|
| 0x00 | 0 | IRR/ISR (OCW3 select) | ICW1 / OCW2 / OCW3 |
| 0x04 | 1 | IMR | ICW2 / ICW3 / ICW4 / OCW1 |

---

## Initialization Command Words (ICW)

### ICW1 (Address 0x00, Write)

| Bit | Name | Description |
|-----|------|-------------|
| 0 | IC4 | ICW4 needed |
| 1 | SNGL | Single mode (no cascade) |
| 2 | ADI | Call address interval |
| 3 | LTIM | Level triggered mode |
| 4 | 1 | Must be 1 (identifies ICW1) |
| 7:5 | A7-A5 | Interrupt vector address (MCS-80) |

### ICW2 (Address 0x04, Write after ICW1)

| Bits | Name | Description |
|------|------|-------------|
| 7:3 | T7-T3 | Interrupt vector base address |
| 2:0 | A10-A8 | Address bits (MCS-80 only) |

### ICW3 (Address 0x04, Write if cascade)

**Master:**
| Bits | Description |
|------|-------------|
| 7:0 | S7-S0: 1=slave on IR[n] |

**Slave:**
| Bits | Description |
|------|-------------|
| 2:0 | Slave ID (0-7) |

### ICW4 (Address 0x04, Write if IC4=1)

| Bit | Name | Description |
|-----|------|-------------|
| 0 | uPM | 1=8086 mode, 0=MCS-80 |
| 1 | AEOI | Auto EOI mode |
| 2 | M/S | Master(1)/Slave(0) buffer |
| 3 | BUF | Buffered mode |
| 4 | SFNM | Special fully nested mode |

---

## Operation Command Words (OCW)

### OCW1 - IMR (Address 0x04)

| Bits | Description |
|------|-------------|
| 7:0 | Interrupt mask (1=masked) |

### OCW2 (Address 0x00)

| Bits | Name | Description |
|------|------|-------------|
| 2:0 | L2-L0 | IR level for specific EOI |
| 4:3 | 00 | OCW2 identifier |
| 7:5 | R,SL,EOI | EOI command type |

**EOI Commands:**
| R | SL | EOI | Command |
|---|----|----|---------|
| 0 | 0 | 1 | Non-specific EOI |
| 0 | 1 | 1 | Specific EOI |
| 1 | 0 | 1 | Rotate on non-specific EOI |
| 1 | 1 | 1 | Rotate on specific EOI |
| 1 | 0 | 0 | Set priority (L=lowest) |
| 1 | 1 | 0 | Rotate on auto EOI (set) |
| 0 | 0 | 0 | Rotate on auto EOI (clear) |

### OCW3 (Address 0x00)

| Bits | Name | Description |
|------|------|-------------|
| 1:0 | RIS,RR | Read register select |
| 2 | P | Poll command |
| 4:3 | 01 | OCW3 identifier |
| 6:5 | ESMM,SMM | Special mask mode |

---

## Internal Registers

### IRR (Interrupt Request Register)
Bits set when interrupt requested, cleared when acknowledged.

### ISR (In-Service Register)
Bits set when interrupt acknowledged, cleared by EOI.

### IMR (Interrupt Mask Register)
1 = Interrupt masked (disabled).

---

**Back to:** [PIC 8259 Specification Index](../pic_8259_index.md)
