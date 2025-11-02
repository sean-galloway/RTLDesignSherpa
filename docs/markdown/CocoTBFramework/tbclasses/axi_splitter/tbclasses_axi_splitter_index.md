# CocoTBFramework/tbclasses/axi_splitter Directory Index

This directory contains AXI splitter testbench components that provide comprehensive verification for AXI transaction splitting functionality. These components handle both read and write AXI transactions that cross memory boundaries and need to be split into multiple smaller transactions.

## Directory Structure

```
CocoTBFramework/tbclasses/axi_splitter/
├── __init__.py
├── axi_read_splitter_packets.py
├── axi_read_splitter_scoreboard.py
├── axi_read_splitter_tb.py
├── axi_write_splitter_packets.py
├── axi_write_splitter_scoreboard.py
└── axi_write_splitter_tb.py
```

## Overview
- [**Overview**](overview.md) - Complete overview of the AXI splitter testbench framework

## Component Documentation

### AXI Read Splitter Components
- [**axi_read_splitter_packets.py**](axi_read_splitter_packets.md) - Packet definitions and field configurations for AXI read transactions
- [**axi_read_splitter_scoreboard.py**](axi_read_splitter_scoreboard.md) - Scoreboard for tracking and verifying AXI read transaction splits
- [**axi_read_splitter_tb.py**](axi_read_splitter_tb.md) - Main testbench for AXI read splitter verification

### AXI Write Splitter Components  
- [**axi_write_splitter_packets.py**](axi_write_splitter_packets.md) - Packet definitions and field configurations for AXI write transactions
- [**axi_write_splitter_scoreboard.py**](axi_write_splitter_scoreboard.md) - Scoreboard for tracking and verifying AXI write transaction splits
- [**axi_write_splitter_tb.py**](axi_write_splitter_tb.md) - Main testbench for AXI write splitter verification

## Quick Start

### Basic Read Splitter Test
```python
from CocoTBFramework.tbclasses.axi_splitter.axi_read_splitter_tb import AxiReadSplitterTB

@cocotb.test()
async def test_read_boundary_crossing(dut):
    tb = AxiReadSplitterTB(dut)
    await tb.initialize()
    
    # Test boundary crossing scenarios
    await tb.run_boundary_crossing_tests()
    await tb.verify_all_transactions()
```

### Basic Write Splitter Test
```python
from CocoTBFramework.tbclasses.axi_splitter.axi_write_splitter_tb import AxiWriteSplitterTB

@cocotb.test()
async def test_write_boundary_crossing(dut):
    tb = AxiWriteSplitterTB(dut)
    await tb.initialize()
    
    # Test write boundary crossing scenarios
    await tb.run_write_boundary_tests()
    await tb.verify_write_transactions()
```

## Key Features

### AXI Read Splitter
- **Boundary Detection**: Automatically detects when read transactions cross memory boundaries
- **Split Verification**: Verifies that large transactions are properly split into smaller boundary-aligned transactions
- **Data Integrity**: Ensures data consistency across split transactions
- **Response Consolidation**: Verifies that split responses are properly combined

### AXI Write Splitter
- **Three-Channel Flow**: Handles AW (address) → W (data) → B (response) channel coordination
- **Write Data Distribution**: Ensures write data is properly distributed across split transactions
- **Response Consolidation**: Verifies single consolidated response per original transaction
- **WLAST Verification**: Validates WLAST signals at split boundaries

## Testing Methodology

### Realistic Address Testing
- **Safe Address Region**: All tests use addresses in safe regions (< MAX_ADDR/2) to avoid wraparound scenarios
- **Boundary Alignment**: Addresses are properly aligned to data width boundaries
- **Dynamic Test Cases**: Test scenarios are generated based on actual data width configurations

### Comprehensive Coverage
- **Boundary Crossing**: Tests transactions that cross various boundary sizes
- **Multiple Data Widths**: Supports testing with 32, 64, 128, 256, and 512-bit data widths
- **Error Detection**: Comprehensive error detection and reporting
- **Timing Verification**: Validates proper timing relationships between channels