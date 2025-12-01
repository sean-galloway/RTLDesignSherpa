# APB GPIO - Register Map

## Register Summary

| Offset | Name | Access | Reset | Description |
|--------|------|--------|-------|-------------|
| 0x000 | GPIO_CONTROL | RW | 0x00000000 | Global control |
| 0x004 | GPIO_DIRECTION | RW | 0x00000000 | Pin direction |
| 0x008 | GPIO_OUTPUT | RW | 0x00000000 | Output data |
| 0x00C | GPIO_INPUT | RO | - | Input data |
| 0x010 | GPIO_INT_ENABLE | RW | 0x00000000 | Interrupt enable |
| 0x014 | GPIO_INT_TYPE | RW | 0x00000000 | Interrupt type |
| 0x018 | GPIO_INT_POLARITY | RW | 0x00000000 | Interrupt polarity |
| 0x01C | GPIO_INT_BOTH | RW | 0x00000000 | Both-edge enable |
| 0x020 | GPIO_INT_STATUS | W1C | 0x00000000 | Interrupt status |

---

## GPIO_CONTROL (0x000)

Global control register.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:1 | Reserved | RO | 0 | Reserved |
| 0 | ENABLE | RW | 0 | GPIO enable (1=enabled) |

---

## GPIO_DIRECTION (0x004)

Pin direction control. Each bit controls one GPIO pin.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | DIR | RW | 0 | Direction per pin (0=input, 1=output) |

---

## GPIO_OUTPUT (0x008)

Output data register. Values driven when pin configured as output.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | DATA | RW | 0 | Output values per pin |

---

## GPIO_INPUT (0x00C)

Input data register. Reflects synchronized external pin values.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | DATA | RO | - | Input values per pin |

**Note:** Value depends on external signals, not reset.

---

## GPIO_INT_ENABLE (0x010)

Interrupt enable register. Controls which pins can generate interrupts.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | IE | RW | 0 | Interrupt enable per pin (1=enabled) |

---

## GPIO_INT_TYPE (0x014)

Interrupt type select. Chooses edge or level sensitivity.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | TYPE | RW | 0 | Type per pin (0=edge, 1=level) |

---

## GPIO_INT_POLARITY (0x018)

Interrupt polarity select.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | POL | RW | 0 | Polarity per pin |

For edge mode: 0=falling, 1=rising
For level mode: 0=active-low, 1=active-high

---

## GPIO_INT_BOTH (0x01C)

Both-edge interrupt enable. Only applicable in edge mode.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | BOTH | RW | 0 | Both edges per pin (1=both edges) |

When set, GPIO_INT_POLARITY is ignored for that pin.

---

## GPIO_INT_STATUS (0x020)

Interrupt status register. Shows pending interrupts.

| Bits | Name | Access | Reset | Description |
|------|------|--------|-------|-------------|
| 31:0 | STATUS | W1C | 0 | Interrupt pending per pin |

**Access:** Read returns current status. Write 1 clears the bit.

---

## Address Calculation

For system address:
```
Register_Address = BASE_ADDR + WINDOW_OFFSET + Register_Offset

Where:
  BASE_ADDR = 0xFEC00000 (RLB base)
  WINDOW_OFFSET = 0x7000 (GPIO window)
  Register_Offset = value from table above

Example:
  GPIO_INPUT = 0xFEC00000 + 0x7000 + 0x00C = 0xFEC0700C
```

---

**Back to:** [GPIO Specification Index](../gpio_index.md)
