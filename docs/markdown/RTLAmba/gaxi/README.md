# GAXI (Generic AXI) Components

This directory contains documentation for GAXI protocol components. GAXI provides a simplified valid/ready handshaking protocol similar to AXI-Stream but with custom extensions.

## Components

### FIFOs

- **[gaxi_drop_fifo_sync](gaxi_drop_fifo_sync.md)** - Synchronous FIFO with drop capability
  - Drop by count (remove N oldest entries)
  - Drop all (flush entire FIFO)
  - 3-cycle drop latency
  - I/O blocking during drop operations
  - WaveDrom timing diagrams included

## Overview

GAXI components use standard valid/ready handshaking:
- **Write Interface**: `wr_valid`, `wr_ready`, `wr_data`
- **Read Interface**: `rd_valid`, `rd_ready`, `rd_data`

Transactions occur when `valid && ready` on the rising edge of the clock.

## Related Documentation

- RTL Source: `rtl/amba/gaxi/`
- Tests: `val/amba/test_gaxi_*.py`
- Testbench Framework: `bin/CocoTBFramework/tbclasses/gaxi/`
