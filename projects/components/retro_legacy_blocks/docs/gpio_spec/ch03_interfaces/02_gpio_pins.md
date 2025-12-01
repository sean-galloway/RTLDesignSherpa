# APB GPIO - GPIO Pin Interface

## Signal Description

### GPIO Signals

| Signal | Width | Dir | Description |
|--------|-------|-----|-------------|
| gpio_out | 32 | O | Output data values |
| gpio_oe | 32 | O | Output enables |
| gpio_in | 32 | I | Input data values |

## Pin Behavior

### Output Mode (direction[i] = 1)

```
                    +--------+
gpio_output[i] ---->| Buffer |----> External Pin
                    |        |
gpio_oe[i] = 1 ---->| Enable |
                    +--------+
```

- gpio_oe[i] = 1 (output enabled)
- gpio_out[i] = GPIO_OUTPUT register value
- Pin driven to output value

### Input Mode (direction[i] = 0)

```
                    +--------+
                    | Buffer |----> External Pin (Hi-Z)
                    |        |
gpio_oe[i] = 0 ---->| Enable |
                    +--------+

External Pin ----> Synchronizer ----> gpio_in[i]
```

- gpio_oe[i] = 0 (tri-state)
- gpio_out[i] = don't care
- External value captured via synchronizer

## Synchronization

### Input Synchronizer

All inputs pass through dual flip-flop synchronizer:

```
          gpio_clk       gpio_clk
             |              |
             v              v
          +-----+        +-----+
gpio_in ->| FF1 |------->| FF2 |-----> synced_input
          +-----+        +-----+
```

- SYNC_STAGES parameter controls depth (default: 2)
- Prevents metastability from asynchronous inputs
- All 32 inputs synchronized in parallel

### Input Latency

Input changes visible in GPIO_INPUT register after:
- SYNC_STAGES cycles of gpio_clk (or pclk if CDC_ENABLE=0)
- Plus APB read latency

## Electrical Considerations

### Output Characteristics

| Parameter | Description |
|-----------|-------------|
| Drive | Standard CMOS output |
| Slew | Defined by I/O cell |
| Protection | ESD per I/O cell design |

### Input Characteristics

| Parameter | Description |
|-----------|-------------|
| Levels | CMOS compatible |
| Hysteresis | Optional per I/O cell |
| Pull-up/down | External to GPIO module |

## Timing Constraints

### Output Path

- gpio_out updates on clock edge
- gpio_oe updates on same clock edge
- No glitch-free guarantee during direction change

### Input Path

- Setup/hold relative to synchronizer clock
- Metastability resolved by synchronizer

---

**Next:** [03_interrupt.md](03_interrupt.md) - Interrupt Interface
