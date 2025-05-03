# AXI Stubs Library

This section contains documentation for SystemVerilog modules that implement AXI stubs for verification and testing of AXI interfaces. These stubs provide simplified interfaces for testing AXI components by packetizing signals and managing handshaking protocols.

## Overview

The AXI stubs library includes modules for both master and slave interfaces, with separate modules for read and write paths, as well as combined modules that handle all five AXI channels. These modules use skid buffers to manage data flow and improve throughput.

## Available Modules

### Complete Stubs
- [AXI Master Stub](axi_master_stub.md) - Complete AXI master stub interface for all five AXI4 channels
- [AXI Slave Stub](axi_slave_stub.md) - Complete AXI slave stub interface for all five AXI4 channels

### Master Components
- [AXI Master Read Stub](axi_master_rd_stub.md) - AXI master read interface stub (AR and R channels)
- [AXI Master Write Stub](axi_master_wr_stub.md) - AXI master write interface stub (AW, W, and B channels)

### Slave Components
- [AXI Slave Read Stub](axi_slave_rd_stub.md) - AXI slave read interface stub (AR and R channels)
- [AXI Slave Write Stub](axi_slave_wr_stub.md) - AXI slave write interface stub (AW, W, and B channels)

## Features

- Configurable skid buffer depths for each channel
- Signal packetization for clean interface to test environment
- Buffer count monitoring for flow control
- Support for all AXI4 features including bursts, quality of service, and user signals

## Usage

These stubs are designed to be used in verification environments for AXI components. They can be instantiated and connected to the device under test (DUT) to provide a simplified interface for generating and monitoring AXI transactions.

## Parameter Naming Conventions

- **Master Stubs**: Use SKID_DEPTH_* parameters (e.g., SKID_DEPTH_AR)
- **Slave Stubs**: Use DEPTH_* parameters (e.g., DEPTH_AR)

## Common Configuration Options

All modules share common AXI parameters:
- AXI_ID_WIDTH: Width of the AXI ID field
- AXI_ADDR_WIDTH: Width of the AXI address bus
- AXI_DATA_WIDTH: Width of the AXI data bus
- AXI_USER_WIDTH: Width of the AXI user field

---

[Return to AMBA Index](../index.md)

---