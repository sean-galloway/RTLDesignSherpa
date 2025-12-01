# APB GPIO - Architecture

## High-Level Block Diagram

![APB GPIO Architecture](../assets/svg/gpio_top.svg)

## Module Hierarchy

```
apb_gpio (Top Level)
+-- apb_slave (OR apb_slave_cdc if CDC_ENABLE=1)
|   +-- APB protocol handling
|   +-- CMD/RSP interface conversion
|   +-- Optional clock domain crossing
|
+-- peakrdl_to_cmdrsp
|   +-- CMD/RSP to PeakRDL regblock adapter
|
+-- gpio_config_regs (Register Wrapper)
    +-- gpio_regs (PeakRDL Generated)
    |   +-- GPIO_CONTROL register
    |   +-- GPIO_DIRECTION register
    |   +-- GPIO_OUTPUT register
    |   +-- GPIO_INPUT register (RO)
    |   +-- GPIO_INT_* registers
    |   +-- GPIO_OUTPUT_SET/CLR/TGL (WO)
    |
    +-- gpio_core (I/O Logic)
        +-- Input synchronization
        +-- Output drivers
        +-- Interrupt detection
        +-- Atomic operations
```

## Data Flow

### Write Transaction Flow

```
1. APB Master Write
   |
   v
2. APB Slave (or APB CDC)
   - Protocol handling
   - Clock domain crossing (if enabled)
   |
   v
3. peakrdl_to_cmdrsp
   - CMD/RSP to regblock conversion
   |
   v
4. gpio_regs (PeakRDL)
   - Register decoding
   - Field updates
   |
   v
5. gpio_config_regs
   - Hardware interface mapping
   |
   v
6. gpio_core
   - Update output registers
   - Update direction
   - Process atomic operations
```

### Read Transaction Flow

```
1. APB Master Read
   |
   v
2. APB Slave (or APB CDC)
   |
   v
3. peakrdl_to_cmdrsp
   |
   v
4. gpio_regs (PeakRDL)
   - Address decode
   - Multiplex read data
   |
   <-- hwif_in (live GPIO state)
   v
5. gpio_core
   - Provide synchronized input
   - Provide current output state
   |
   v
6. PRDATA returned to master
```

### Interrupt Flow

```
1. External Pin Change
   |
   v
2. gpio_core
   - Input synchronization (2-stage FF)
   - Edge/level detection
   |
   v
3. Interrupt Logic
   - Compare with INT_TYPE, INT_POLARITY, INT_BOTH
   - Apply INT_ENABLE mask
   |
   v
4. GPIO_INT_STATUS
   - Set corresponding bit (sticky)
   |
   v
5. irq Output
   - OR of all unmasked, enabled interrupt sources
   |
   v
6. Software reads GPIO_INT_STATUS
   - Writes 1 to clear (W1C)
```

## Clock Domains

### Synchronous Mode (CDC_ENABLE = 0)

```
APB Clock Domain (pclk)
+-- apb_slave
+-- peakrdl_to_cmdrsp
+-- gpio_config_regs
+-- gpio_regs
+-- gpio_core

All modules use pclk
Input synchronization still active for external pins
```

### Asynchronous Mode (CDC_ENABLE = 1)

```
APB Clock Domain (pclk)
+-- apb_slave_cdc (pclk side)
+-- [CDC boundary with skid buffers]

GPIO Clock Domain (gpio_clk)
+-- apb_slave_cdc (gpio_clk side)
+-- peakrdl_to_cmdrsp
+-- gpio_config_regs
+-- gpio_regs
+-- gpio_core
```

## Parameterization

| Parameter | Type | Default | Description |
|-----------|------|---------|-------------|
| `GPIO_WIDTH` | int | 32 | Number of GPIO pins |
| `SYNC_STAGES` | int | 2 | Input synchronizer stages |
| `CDC_ENABLE` | int | 0 | Enable clock domain crossing |
| `SKID_DEPTH` | int | 2 | CDC skid buffer depth |

## Resource Estimates

| Component | Flip-Flops | LUTs |
|-----------|-----------|------|
| gpio_core | ~200 | ~300 |
| gpio_regs | ~400 | ~200 |
| gpio_config_regs | ~50 | ~100 |
| apb_slave (no CDC) | ~20 | ~50 |
| apb_slave_cdc | ~100 | ~150 |
| **Total (no CDC)** | ~670 | ~650 |
| **Total (with CDC)** | ~750 | ~750 |

---

**Next:** [03_clocks_and_reset.md](03_clocks_and_reset.md) - Clock and reset behavior
