# APB PIC 8259 - Overview

## Introduction

The APB PIC 8259 is an 8259A-compatible Programmable Interrupt Controller with an APB interface. It provides interrupt management for legacy PC-compatible systems.

## Key Features

- 8 interrupt inputs per controller
- Master/Slave cascade support
- Programmable priority modes
- Edge or level triggering
- Automatic EOI option
- Interrupt masking
- Polling mode support
- Special fully nested mode

## Applications

- PC-compatible interrupt management
- Legacy device support
- x86 system integration

## Block Diagram

![PIC 8259 Block Diagram](../assets/svg/pic_8259_top.svg)

## Register Summary

| Offset | A0 | Read | Write |
|--------|-----|------|-------|
| 0x00 | 0 | IRR/ISR | ICW1/OCW2/OCW3 |
| 0x04 | 1 | IMR | ICW2/ICW3/ICW4/OCW1 |

## Interrupt Priority

| IRQ | Default Priority |
|-----|-----------------|
| IR0 | Highest (0) |
| IR1 | 1 |
| IR2 | 2 (cascade in master) |
| IR3 | 3 |
| IR4 | 4 |
| IR5 | 5 |
| IR6 | 6 |
| IR7 | Lowest (7) |

## Priority Modes

- **Fixed Priority**: IR0 highest, IR7 lowest
- **Rotating Priority**: Lowest priority rotates after EOI
- **Specific Priority**: Programmable lowest priority

---

**Next:** [02_architecture.md](02_architecture.md)
