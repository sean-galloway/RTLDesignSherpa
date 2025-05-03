# AXIL Modules Documentation

This section contains documentation for Advanced eXtensible Interface Lite (AXI-Lite) modules, which are SystemVerilog implementations of the AXI4-Lite protocol interfaces. AXI-Lite is a simplified version of the AXI4 protocol designed for simple control register-style interfaces with reduced complexity.

## Overview

The AXIL modules provide comprehensive implementations of AXI4-Lite master and slave interfaces with the following features:

- **Complete Channel Support**: All five AXI-Lite channels (AW, W, B, AR, R) with proper handshaking
- **Configurable Buffering**: Skid buffers for all channels with adjustable depths
- **Error Monitoring**: Comprehensive error detection and reporting via dedicated FIFOs
- **Clock Gating Options**: Power-saving variants with intelligent clock gating capability
- **Timeout Detection**: Configurable timeout thresholds for all channels

## Module Categories

### Master Interfaces

These modules implement AXI-Lite master functionality (initiating transactions):

- [axil_master](axil_master.md) - Standard AXI-Lite master interface
- [axil_master_cg](axil_master_cg.md) - AXI-Lite master interface with clock gating
- [axil_master_rd](axil_master_rd.md) - Read-only AXI-Lite master (AR/R channels)
- [axil_master_rd_cg](axil_master_rd_cg.md) - Read-only AXI-Lite master with clock gating
- [axil_master_wr](axil_master_wr.md) - Write-only AXI-Lite master (AW/W/B channels)
- [axil_master_wr_cg](axil_master_wr_cg.md) - Write-only AXI-Lite master with clock gating

### Slave Interfaces

These modules implement AXI-Lite slave functionality (responding to transactions):

- [axil_slave](axil_slave.md) - Standard AXI-Lite slave interface
- [axil_slave_cg](axil_slave_cg.md) - AXI-Lite slave interface with clock gating
- [axil_slave_rd](axil_slave_rd.md) - Read-only AXI-Lite slave (AR/R channels)
- [axil_slave_rd_cg](axil_slave_rd_cg.md) - Read-only AXI-Lite slave with clock gating
- [axil_slave_wr](axil_slave_wr.md) - Write-only AXI-Lite slave (AW/W/B channels)
- [axil_slave_wr_cg](axil_slave_wr_cg.md) - Write-only AXI-Lite slave with clock gating

## Implementation Patterns

The modules follow consistent design patterns:

1. **Top-Level Modules**: `axil_master`, `axil_master_cg`, `axil_slave`, and `axil_slave_cg` integrate separate read and write path modules.
   
2. **Read Path Modules**: `axil_master_rd`, `axil_master_rd_cg`, `axil_slave_rd`, and `axil_slave_rd_cg` handle AR and R channels.
   
3. **Write Path Modules**: `axil_master_wr`, `axil_master_wr_cg`, `axil_slave_wr`, and `axil_slave_wr_cg` handle AW, W, and B channels.
   
4. **Clock Gating Variants**: Modules with `_cg` suffix add power-saving capabilities through intelligent clock gating.

## Key Features

### Configurable Parameters

All modules offer extensive parameterization:

- **Bus Widths**: Configurable address and data widths
- **Buffer Depths**: Adjustable skid buffer sizes for performance tuning
- **Timeout Values**: Configurable timeout periods for each channel
- **Clock Gating Control**: Adjustable idle threshold for power optimization (in CG variants)

### Error Handling

Comprehensive error detection and reporting:

- **Timeout Detection**: For all AXI-Lite channels
- **Response Error Handling**: SLVERR and DECERR detection
- **Error Reporting**: Dedicated FIFO interfaces for error notification

### Performance Optimization

Features for improved performance:

- **Skid Buffers**: Improve timing and throughput
- **Proper Flow Control**: Handle backpressure efficiently
- **Pipeline Breaking**: Improve timing closure

### Power Optimization

Clock gating variants provide:

- **Dynamic Power Reduction**: Clock gating during idle periods
- **Configurable Idle Threshold**: Adjustable trade-off between power saving and wake-up latency
- **Status Reporting**: Signals for monitoring gating activity

---

[Return to AMBA Index](../index.md)

---