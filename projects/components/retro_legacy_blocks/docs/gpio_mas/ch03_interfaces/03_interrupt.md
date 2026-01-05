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

# APB GPIO - Interrupt Interface

## Signal Description

| Signal | Width | Dir | Description |
|--------|-------|-----|-------------|
| irq | 1 | O | Interrupt request (active high) |

## Interrupt Generation

### Aggregate Logic

```
irq = |(GPIO_INT_STATUS[31:0] & GPIO_INT_ENABLE[31:0])
```

IRQ is asserted when any enabled interrupt source is active.

### Per-Pin Configuration

Each GPIO pin can generate interrupts independently:

| Register | Function |
|----------|----------|
| GPIO_INT_ENABLE | Enable/disable per pin |
| GPIO_INT_TYPE | Edge (0) or Level (1) |
| GPIO_INT_POLARITY | Falling/Low (0) or Rising/High (1) |
| GPIO_INT_BOTH | Both edges (edge mode only) |
| GPIO_INT_STATUS | Current interrupt status |

## Interrupt Modes

### Edge-Triggered

```
GPIO_INT_TYPE[i] = 0

        synced_input
              |
              v
         +----------+
         | Edge     |
         | Detect   |---> Set STATUS[i]
         +----------+
              ^
              |
    Polarity/Both Config
```

- Captures transitions on synchronized input
- Status bit latches until cleared by software
- Both-edge mode ignores polarity setting

### Level-Sensitive

```
GPIO_INT_TYPE[i] = 1

        synced_input
              |
              v
         +----------+
         | Level    |
         | Compare  |---> STATUS[i]
         +----------+
              ^
              |
    Polarity Config
```

- Continuously compares input to polarity
- Status follows input level
- Re-triggers if not cleared while active

## Interrupt Timing

### Edge-Triggered Latency

```
External event --> Synchronizer --> Edge detect --> STATUS set --> IRQ
                   (2 cycles)      (1 cycle)       (1 cycle)

Total: 4 clock cycles typical
```

### Level-Sensitive Latency

```
External level --> Synchronizer --> Level compare --> IRQ
                   (2 cycles)       (1 cycle)

Total: 3 clock cycles typical
```

## Interrupt Handling

### Software Sequence

1. IRQ asserts (hardware)
2. CPU vectors to interrupt handler
3. Read GPIO_INT_STATUS to identify sources
4. Handle interrupt condition
5. Write 1 to GPIO_INT_STATUS bits to clear
6. IRQ deasserts if no other sources

### Clearing Interrupts

| Mode | Clear Method |
|------|--------------|
| Edge | Write 1 to STATUS bit |
| Level | Clear source, then write 1 to STATUS |

## Connection Guidelines

- Connect to interrupt controller input
- Active-high, level-sensitive recommended at controller
- Single IRQ covers all 32 GPIO pins

---

**Next:** [04_system.md](04_system.md) - System Interface
