# APB GPIO - APB Interface Block

## Overview

The APB interface provides the connection between the system APB bus and the GPIO register file.

## Block Diagram

![APB Interface Block](../assets/svg/gpio_interfaces.svg)

## Interface Signals

### APB Slave Interface

| Signal | Width | Direction | Description |
|--------|-------|-----------|-------------|
| s_apb_psel | 1 | Input | Slave select |
| s_apb_penable | 1 | Input | Enable phase |
| s_apb_pwrite | 1 | Input | Write operation |
| s_apb_paddr | 12 | Input | Address bus |
| s_apb_pwdata | 32 | Input | Write data |
| s_apb_pstrb | 4 | Input | Byte strobes |
| s_apb_prdata | 32 | Output | Read data |
| s_apb_pready | 1 | Output | Ready response |
| s_apb_pslverr | 1 | Output | Error response |

## Operation

### Read Transaction
1. Master asserts `psel` and `paddr`
2. Master asserts `penable` on next cycle
3. Slave returns `prdata` with `pready`

### Write Transaction
1. Master asserts `psel`, `paddr`, `pwdata`, `pwrite`
2. Master asserts `penable` on next cycle
3. Slave samples data with `pready`

## Timing Diagram

```
         _____       _____       _____
pclk  __/     \_____/     \_____/     \_____

         _________________
psel  __/                 \_________________

                   _______
penable __________|       |_________________

paddr   XXXXXXXXXX|  ADDR |XXXXXXXXXXXXXXXXX

prdata  XXXXXXXXXX|  DATA |XXXXXXXXXXXXXXXXX
                   _______
pready  __________|       |_________________
```

## Implementation Notes

- Zero wait-state operation for all registers
- No error responses (pslverr always 0)
- 32-bit aligned access only

---

**Next:** [02_register_file.md](02_register_file.md) - Register File
