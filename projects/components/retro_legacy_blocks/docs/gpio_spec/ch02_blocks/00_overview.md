# APB GPIO - Block Descriptions Overview

## Module Hierarchy

```
apb_gpio
|-- APB Interface (apb_slave integration)
|-- Register File (PeakRDL generated)
|-- GPIO Core
|   |-- Input Synchronizer
|   |-- Output Control
|   |-- Direction Control
|   |-- Interrupt Logic
|-- CDC Logic (optional)
```

## Block Summary

| Block | File | Description |
|-------|------|-------------|
| APB GPIO Top | apb_gpio.sv | Top-level module with all GPIO functionality |
| Register File | apb_gpio_regs.sv | PeakRDL-generated control/status registers |

## Detailed Block Descriptions

### 1. APB Interface
Handles APB protocol conversion and register access.

**See:** [01_apb_interface.md](01_apb_interface.md)

### 2. Register File
PeakRDL-generated registers for configuration and status.

**See:** [02_register_file.md](02_register_file.md)

### 3. GPIO Core
Main GPIO functionality including I/O control and interrupts.

**See:** [03_gpio_core.md](03_gpio_core.md)

### 4. Interrupt Controller
Edge detection, level sensing, and interrupt aggregation.

**See:** [04_interrupt_controller.md](04_interrupt_controller.md)

### 5. CDC Logic
Optional clock domain crossing for asynchronous GPIO clock.

**See:** [05_cdc_logic.md](05_cdc_logic.md)

---

**Next:** [01_apb_interface.md](01_apb_interface.md) - APB Interface details
