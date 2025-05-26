# APB (Advanced Peripheral Bus) Modules

## Overview

The APB (Advanced Peripheral Bus) is a simple, low-bandwidth protocol from the AMBA (Advanced Microcontroller Bus Architecture) family, designed for connecting peripherals with minimal power and complexity requirements. This collection includes various SystemVerilog implementations of APB interfaces with different features and optimizations.

The modules in this collection provide:
- Standard APB master and slave interfaces
- Clock domain crossing (CDC) capabilities for multi-clock designs
- Clock gating (CG) for power optimization
- Stub versions for simplified interconnect or testing scenarios

Each module follows the APB protocol specification while providing additional features for specific use cases. They all use a command/response interface pattern to simplify integration with user logic.

## Available Modules

### Master Interfaces

- [APB Master](apb_master.md) - Standard APB master implementation with command/response interface
- [APB Master with Clock Gating](apb_master_cg.md) - Power-optimized version with clock gating
- [APB Master Stub](apb_master_stub.md) - Simplified master interface with packed data formats

### Slave Interfaces

- [APB Slave](apb_slave.md) - Standard APB slave implementation with command/response interface
- [APB Slave with Clock Gating](apb_slave_cg.md) - Power-optimized version with clock gating
- [APB Slave with Clock Domain Crossing](apb_slave_cdc.md) - Multi-clock domain interface
- [APB Slave with CDC and Clock Gating](apb_slave_cdc_cg.md) - Combined CDC and power optimization
- [APB Slave Stub](apb_slave_stub.md) - Simplified slave interface with packed data formats

## Common Features

All modules in this collection share these common features:
- Configurable address and data widths
- FIFO buffering for commands and responses
- Proper APB protocol timing compliance
- Parameterizable FIFO depths for performance tuning

---

[Return to AMBA Index](../index.md)

---