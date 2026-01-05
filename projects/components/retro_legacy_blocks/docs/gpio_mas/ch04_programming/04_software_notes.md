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

# APB GPIO - Software Considerations

## Performance

### Register Access Timing

| Operation | APB Cycles | Notes |
|-----------|------------|-------|
| Read | 2 | Setup + access |
| Write | 2 | Setup + access |
| Read-Modify-Write | 4 | Read + write |

### Optimizing Access

**Batch operations when possible:**
```c
// Inefficient - 4 separate writes
GPIO_OUTPUT |= (1 << 0);
GPIO_OUTPUT |= (1 << 1);
GPIO_OUTPUT |= (1 << 2);
GPIO_OUTPUT |= (1 << 3);

// Efficient - single write
GPIO_OUTPUT |= 0x0000000F;
```

**Cache register values:**
```c
// Inefficient - 4 reads + 4 writes
for (int i = 0; i < 4; i++) {
    GPIO_DIRECTION |= (1 << i);
}

// Efficient - 1 read + 1 write
uint32_t dir = GPIO_DIRECTION;
dir |= 0x0000000F;
GPIO_DIRECTION = dir;
```

## Synchronization

### Input Latency

GPIO inputs have inherent latency:
- SYNC_STAGES clock cycles (default 2)
- Plus software polling/interrupt overhead

**Account for latency in timing-critical code.**

### Volatile Registers

Always declare GPIO registers as volatile:
```c
#define GPIO_INPUT  (*(volatile uint32_t *)0xFEC0700C)
```

### Multi-Core Considerations

If multiple cores access GPIO:
```c
// Use atomic operations or locks
spin_lock(&gpio_lock);
uint32_t val = GPIO_OUTPUT;
val |= new_bits;
GPIO_OUTPUT = val;
spin_unlock(&gpio_lock);
```

## Interrupt Best Practices

### Clear Before Return

Always clear interrupt status before ISR return:
```c
void gpio_isr(void) {
    uint32_t status = GPIO_INT_STATUS;
    // Handle interrupts
    GPIO_INT_STATUS = status;  // Must clear!
}
```

### Avoid Spurious Interrupts

Disable interrupts during configuration:
```c
void reconfigure_interrupt(int pin) {
    uint32_t mask = (1 << pin);

    // Disable first
    GPIO_INT_ENABLE &= ~mask;

    // Reconfigure
    // ...

    // Clear any pending
    GPIO_INT_STATUS = mask;

    // Re-enable
    GPIO_INT_ENABLE |= mask;
}
```

### Level-Sensitive Caution

Level interrupts can cause interrupt storms:
```c
void level_isr(void) {
    // WRONG - will re-trigger immediately
    GPIO_INT_STATUS = status;

    // RIGHT - handle source first
    clear_external_interrupt_source();
    GPIO_INT_STATUS = status;
}
```

## Error Handling

### No Hardware Errors

GPIO controller doesn't generate errors:
- All addresses valid
- pslverr always 0

### Software Validation

Validate configuration in software:
```c
bool gpio_set_direction(uint32_t pin, bool output) {
    if (pin >= 32) return false;

    if (output) {
        GPIO_DIRECTION |= (1 << pin);
    } else {
        GPIO_DIRECTION &= ~(1 << pin);
    }
    return true;
}
```

## Debug Tips

### Read-Back Verification

```c
void gpio_debug(void) {
    printf("CONTROL:   0x%08X\n", GPIO_CONTROL);
    printf("DIRECTION: 0x%08X\n", GPIO_DIRECTION);
    printf("OUTPUT:    0x%08X\n", GPIO_OUTPUT);
    printf("INPUT:     0x%08X\n", GPIO_INPUT);
    printf("INT_STAT:  0x%08X\n", GPIO_INT_STATUS);
}
```

### Loopback Testing

Connect output to input for self-test:
```c
bool gpio_loopback_test(int out_pin, int in_pin) {
    GPIO_DIRECTION |= (1 << out_pin);
    GPIO_DIRECTION &= ~(1 << in_pin);

    // Test high
    GPIO_OUTPUT |= (1 << out_pin);
    delay_us(10);  // Allow synchronization
    if (!(GPIO_INPUT & (1 << in_pin))) return false;

    // Test low
    GPIO_OUTPUT &= ~(1 << out_pin);
    delay_us(10);
    if (GPIO_INPUT & (1 << in_pin)) return false;

    return true;
}
```

---

**Back to:** [00_overview.md](00_overview.md) - Programming Model Overview

**Next Chapter:** [Chapter 5: Registers](../ch05_registers/01_register_map.md)
