<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# CocoTBFramework/tbclasses/gaxi Directory Index

This directory contains GAXI (Generic AXI-like) testbench classes for the CocoTBFramework. These components provide comprehensive testbench functionality for GAXI buffer components, data collection modules, and protocol verification.

## Directory Structure

```
CocoTBFramework/tbclasses/gaxi/
├── gaxi_buffer.py
├── gaxi_buffer_configs.py
├── gaxi_buffer_field.py
├── gaxi_buffer_multi.py
├── gaxi_buffer_multi_sigmap.py
├── gaxi_buffer_seq.py
└── gaxi_data_collect_tb.py
```

## Overview
- [**Overview**](tbclasses_gaxi_gaxi_overview.md) - Complete overview of GAXI testbench components

## Component Documentation

### Core Buffer Testbenches
- [**gaxi_buffer.py**](tbclasses_gaxi_gaxi_buffer.md) - Basic GAXI buffer testbench with FlexConfigGen integration
- [**gaxi_buffer_field.py**](tbclasses_gaxi_gaxi_buffer_field.md) - Field-based GAXI buffer testbench for multi-field testing
- [**gaxi_buffer_multi.py**](tbclasses_gaxi_gaxi_buffer_multi.md) - Multi-signal GAXI buffer testbench with enhanced timing
- [**gaxi_buffer_multi_sigmap.py**](tbclasses_gaxi_gaxi_buffer_multi_sigmap.md) - Multi-signal GAXI buffer testbench with signal mapping

### Configuration and Sequences
- [**gaxi_buffer_configs.py**](tbclasses_gaxi_gaxi_buffer_configs.md) - Shared field configurations for GAXI buffer tests
- [**gaxi_buffer_seq.py**](tbclasses_gaxi_gaxi_buffer_seq.md) - Extended sequence generators for GAXI buffer testing

### Specialized Testbenches
- [**gaxi_data_collect_tb.py**](tbclasses_gaxi_gaxi_data_collect_tb.md) - Enhanced testbench for GAXI data collection modules

## Quick Start

### Basic GAXI Buffer Testing
```python
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer import GaxiBufferTB

@cocotb.test()
async def test_basic_buffer(dut):
    # Environment setup
    os.environ['TEST_DEPTH'] = '16'
    os.environ['TEST_DATA_WIDTH'] = '32'
    os.environ['TEST_MODE'] = 'skid'
    
    # Create testbench
    tb = GaxiBufferTB(dut, wr_clk=dut.clk, wr_rstn=dut.rstn)
    await tb.initialize()
    
    # Run basic test
    await tb.basic_test(num_packets=50)
```

### Field-Based Testing
```python
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_field import GaxiFieldBufferTB

@cocotb.test()
async def test_field_buffer(dut):
    # Environment setup for field testing
    os.environ['TEST_ADDR_WIDTH'] = '16'
    os.environ['TEST_CTRL_WIDTH'] = '8'
    os.environ['TEST_DATA_WIDTH'] = '32'
    
    # Create field-based testbench
    tb = GaxiFieldBufferTB(dut, wr_clk=dut.clk, wr_rstn=dut.rstn)
    await tb.initialize()
    
    # Run field-specific tests
    await tb.test_field_patterns(num_patterns=25)
```

### Multi-Signal Buffer Testing
```python
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_multi import GaxiMultiBufferTB

@cocotb.test()
async def test_multi_buffer(dut):
    # Multi-signal environment setup
    os.environ['TEST_DEPTH'] = '32'
    os.environ['TEST_ADDR_WIDTH'] = '32'
    os.environ['TEST_CTRL_WIDTH'] = '8'
    os.environ['TEST_DATA_WIDTH'] = '64'
    
    # Create multi-signal testbench
    tb = GaxiMultiBufferTB(dut, wr_clk=dut.clk, wr_rstn=dut.rstn)
    await tb.initialize()
    
    # Run comprehensive multi-signal tests
    await tb.test_concurrent_streams(num_packets=100)
```

## Environment Variables

All GAXI testbenches use environment variables for configuration:

### Common Variables
- `TEST_DEPTH`: Buffer depth (default: varies by component)
- `TEST_DATA_WIDTH`: Data width in bits (default: 32)
- `TEST_MODE`: Buffer mode ('skid', 'fifo', etc.)
- `TEST_KIND`: Timing mode ('sync', 'async')
- `TEST_CLK_WR`: Write clock period (default: 10)
- `TEST_CLK_RD`: Read clock period (default: 10)

### Field-Specific Variables
- `TEST_ADDR_WIDTH`: Address field width
- `TEST_CTRL_WIDTH`: Control field width
- Multi-field components support separate width configuration

## Architecture Features

### Unified Infrastructure
- All testbenches use **GAXIComponentBase** infrastructure
- Consistent **FieldConfig** patterns for field management
- **FlexConfigGen** integration for comprehensive randomization
- **MemoryModel** integration for verification

### Enhanced Timing
- Fixed timing issues with proper completion checking
- Timeout protection to prevent infinite waits
- Buffer-depth-aware delay calculations
- Mode-specific timing optimizations

### Randomization Profiles
- **FlexConfigGen** provides multiple randomization profiles
- Configurable constraints for realistic testing
- Profile-based testing for corner cases
- Enhanced sequence generation capabilities

## Supported DUT Types

### Buffer Components
- `gaxi_fifo_sync`: Synchronous FIFO buffer
- `gaxi_fifo_sync_multi`: Multi-signal synchronous FIFO
- `gaxi_fifo_sync_field`: Field-based synchronous FIFO
- `gaxi_skid_buffer`: Skid buffer implementation
- `gaxi_skid_buffer_multi`: Multi-signal skid buffer
- `gaxi_skid_buffer_field`: Field-based skid buffer

### Data Collection Components
- `gaxi_data_collect`: Multi-channel data collection with arbitration
- Supports channel-based data aggregation and validation

## Testing Methodologies

### Comprehensive Test Coverage
- **Basic functionality**: Read/write operations, handshake validation
- **Boundary conditions**: Full/empty buffer states, back-to-back operations
- **Stress testing**: High-frequency operations, random delays
- **Protocol compliance**: Valid/ready handshake verification
- **Corner cases**: Reset during operation, X/Z value handling

### Verification Strategies
- **Memory-based verification**: Expected vs. actual data comparison
- **Scoreboard integration**: Transaction-level verification
- **Statistical analysis**: Performance metrics and timing analysis
- **Error injection**: Fault tolerance testing

## Integration Points

### Framework Integration
- Compatible with CocoTBFramework component architecture
- Integrates with shared scoreboards and transformers
- Uses framework utilities for path management and logging
- Supports framework statistics aggregation

### External Tool Integration
- Waveform generation for debug visualization
- Log file integration for comprehensive debugging
- Support for multiple simulators (VCS, Questasim, etc.)
- Integration with external verification methodologies