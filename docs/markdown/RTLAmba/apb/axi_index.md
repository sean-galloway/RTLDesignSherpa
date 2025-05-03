# AMBA AXI Module Index

[Return to AMBA Index](../index.md)

## Overview

This documentation covers a comprehensive set of SystemVerilog modules implementing AMBA AXI4 interfaces with advanced features for high-performance SoC interconnects. The modules are divided into master and slave interfaces, each with standard and power-optimized (clock-gated) variants.

These AXI modules provide:

- Complete implementation of AXI4 protocol
- Transaction splitting across memory alignment boundaries
- Comprehensive error monitoring and reporting
- Configurable buffering through parameterized skid buffers
- Power optimization through fine-grained clock gating (CG variants)

## Master Modules

Master interfaces initiate AXI transactions and include transaction splitting to ensure memory alignment requirements are met.

- [axi_master](axi_master.md) - Top-level AXI master interface with comprehensive transaction support
- [axi_master_cg](axi_master_cg.md) - Clock-gated version of the AXI master interface
- [axi_master_rd](axi_master_rd.md) - AXI master read controller managing read transactions
- [axi_master_rd_cg](axi_master_rd_cg.md) - Clock-gated version of the AXI master read controller
- [axi_master_rd_splitter](axi_master_rd_splitter.md) - Transaction splitter for read operations
- [axi_master_wr](axi_master_wr.md) - AXI master write controller managing write transactions
- [axi_master_wr_cg](axi_master_wr_cg.md) - Clock-gated version of the AXI master write controller
- [axi_master_wr_splitter](axi_master_wr_splitter.md) - Transaction splitter for write operations

## Slave Modules

Slave interfaces respond to AXI transactions and provide bridges to memory or peripheral logic.

- [axi_slave](axi_slave.md) - Top-level AXI slave interface with comprehensive transaction support
- [axi_slave_cg](axi_slave_cg.md) - Clock-gated version of the AXI slave interface
- [axi_slave_rd](axi_slave_rd.md) - AXI slave read controller managing read transactions
- [axi_slave_rd_cg](axi_slave_rd_cg.md) - Clock-gated version of the AXI slave read controller
- [axi_slave_wr](axi_slave_wr.md) - AXI slave write controller managing write transactions
- [axi_slave_wr_cg](axi_slave_wr_cg.md) - Clock-gated version of the AXI slave write controller

## Key Features

### Transaction Splitting

Both master read and write paths include dedicated splitter modules that divide transactions crossing memory alignment boundaries into multiple smaller transactions. This ensures optimal memory access patterns and compliance with system constraints such as 4KB page boundaries.

### Clock Gating (CG Variants)

All modules have clock-gated variants that monitor channel activity and gate the clock when idle, significantly reducing power consumption in large SoC designs. These variants include configurable idle detection thresholds and status outputs for power optimization.

### Error Monitoring

All modules integrate comprehensive error monitoring with timeout detection on each AXI channel and error response tracking. Dedicated FIFO interfaces report detected errors with associated transaction information.

### Buffering

All modules implement configurable-depth skid buffers for improved performance, timing closure, and throughput. Buffer depths can be tuned based on expected traffic patterns.

## Parameter Customization

All modules support extensive parameterization including:

- AXI bus widths (ID, address, data, user fields)
- Skid buffer depths
- Timeout values
- FIFO depths
- Clock gating parameters

[Return to AMBA Index](../index.md)
