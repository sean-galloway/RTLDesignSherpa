# APB GPIO - Overview

## Introduction

The APB GPIO controller provides a 32-bit general-purpose I/O interface with APB bus connectivity. It enables software-controlled digital I/O with flexible interrupt generation capabilities.

## Features

### Core Functionality
- 32-bit bidirectional GPIO port
- Per-bit direction control (input/output)
- Per-bit output enable control
- Input synchronization for metastability protection

### Interrupt Capabilities
- Per-bit interrupt enable
- Edge-triggered interrupts (rising, falling, or both)
- Level-triggered interrupts (high or low)
- Combined interrupt output (OR of all enabled sources)
- Write-1-to-clear interrupt status

### Atomic Operations
- Atomic set (OR with mask)
- Atomic clear (AND with inverted mask)
- Atomic toggle (XOR with mask)
- No read-modify-write race conditions

### Clock Domain Crossing
- Optional CDC support via `CDC_ENABLE` parameter
- Separate GPIO clock domain for async I/O
- Multi-stage input synchronization

## Applications

### Typical Use Cases
- LED control and status indication
- Push-button and switch inputs
- External device reset control
- Interrupt generation from external events
- Bit-banged serial protocols (I2C, SPI fallback)
- Debug signals and test points

### System Integration
- Memory-mapped APB peripheral
- Single interrupt line to CPU/interrupt controller
- Direct connection to FPGA I/O pads via IOBUFs
- Compatible with standard GPIO software drivers

## Block Diagram

```
+------------------------------------------------------------------+
|                          APB GPIO                                  |
|                                                                    |
|  +----------------+     +------------------+     +-------------+   |
|  |   APB Slave    |---->| gpio_config_regs |---->|  gpio_core  |   |
|  | (Optional CDC) |     |                  |     |             |   |
|  +----------------+     +------------------+     +-------------+   |
|         ^                       |                      |           |
|         |                       v                      v           |
|    APB Bus               Register File           GPIO Pins         |
|                          (PeakRDL)              gpio_in[31:0]      |
|                                                 gpio_out[31:0]     |
|                                                 gpio_oe[31:0]      |
|                                                      |             |
|                                                      v             |
|                                                    irq             |
+------------------------------------------------------------------+
```

## Key Specifications

| Parameter | Value |
|-----------|-------|
| GPIO Width | 32 bits (configurable) |
| APB Data Width | 32 bits |
| APB Address Width | 12 bits (4KB) |
| Sync Stages | 2 (configurable) |
| CDC Support | Optional |

## Register Summary

| Address | Register | Description |
|---------|----------|-------------|
| 0x000 | GPIO_CONTROL | Global enable and interrupt enable |
| 0x004 | GPIO_DIRECTION | Per-bit direction (1=output) |
| 0x008 | GPIO_OUTPUT | Output data value |
| 0x00C | GPIO_INPUT | Input data (read-only) |
| 0x010 | GPIO_INT_ENABLE | Per-bit interrupt enable |
| 0x014 | GPIO_INT_TYPE | Interrupt type (1=level, 0=edge) |
| 0x018 | GPIO_INT_POLARITY | Polarity (1=high/rising) |
| 0x01C | GPIO_INT_BOTH | Both-edge enable |
| 0x020 | GPIO_INT_STATUS | Interrupt status (W1C) |
| 0x024 | GPIO_RAW_INT | Raw interrupt (pre-mask) |
| 0x028 | GPIO_OUTPUT_SET | Atomic set |
| 0x02C | GPIO_OUTPUT_CLR | Atomic clear |
| 0x030 | GPIO_OUTPUT_TGL | Atomic toggle |

---

**Next:** [02_architecture.md](02_architecture.md) - High-level architecture
