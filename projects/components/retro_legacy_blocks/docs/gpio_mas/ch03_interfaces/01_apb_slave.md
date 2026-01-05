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

# APB GPIO - APB Slave Interface

## Signal Description

### APB Slave Signals

| Signal | Width | Dir | Description |
|--------|-------|-----|-------------|
| pclk | 1 | I | APB clock |
| presetn | 1 | I | APB reset (active low) |
| s_apb_psel | 1 | I | Peripheral select |
| s_apb_penable | 1 | I | Enable phase |
| s_apb_pwrite | 1 | I | Write transaction |
| s_apb_paddr | 12 | I | Address bus |
| s_apb_pwdata | 32 | I | Write data |
| s_apb_pstrb | 4 | I | Byte strobes |
| s_apb_prdata | 32 | O | Read data |
| s_apb_pready | 1 | O | Ready response |
| s_apb_pslverr | 1 | O | Slave error |

## Protocol Compliance

### APB3/APB4 Features

| Feature | Support |
|---------|---------|
| PSEL | Yes |
| PENABLE | Yes |
| PWRITE | Yes |
| PADDR | 12-bit |
| PWDATA | 32-bit |
| PRDATA | 32-bit |
| PREADY | Yes (always 1) |
| PSLVERR | Yes (always 0) |
| PSTRB | Yes |
| PPROT | No |

## Timing

### Zero Wait State

All register accesses complete in minimum APB cycles:
- Read: 2 cycles (setup + access)
- Write: 2 cycles (setup + access)

### Timing Diagram

```
          ___     ___     ___     ___
pclk    _|   |___|   |___|   |___|   |___

        _______________
psel   |               |_________________

                _______
penable ________|       |________________

paddr   --------|  A1   |----------------

pwdata  --------|  D1   |---------------- (write)

prdata  --------|  D1   |---------------- (read)
                _______
pready  ________|       |________________
```

## Address Decoding

### Address Map

| Address | Register | Access |
|---------|----------|--------|
| 0x000 | GPIO_CONTROL | RW |
| 0x004 | GPIO_DIRECTION | RW |
| 0x008 | GPIO_OUTPUT | RW |
| 0x00C | GPIO_INPUT | RO |
| 0x010 | GPIO_INT_ENABLE | RW |
| 0x014 | GPIO_INT_TYPE | RW |
| 0x018 | GPIO_INT_POLARITY | RW |
| 0x01C | GPIO_INT_BOTH | RW |
| 0x020 | GPIO_INT_STATUS | W1C |

### Byte Strobes

Byte-granular writes supported:
- pstrb[3:0] corresponds to pwdata[31:0]
- Unselected bytes retain previous values

## Error Handling

- No address decode errors (all addresses valid)
- No timeout errors
- pslverr always 0

---

**Next:** [02_gpio_pins.md](02_gpio_pins.md) - GPIO Pin Interface
