# GAXI Testbenches

## Overview

The `tbclasses/gaxi` module provides testbench classes for verifying Generic AXI (GAXI) buffer implementations and interfaces. These testbenches leverage the GAXI components to create comprehensive verification environments for various AXI-style components including skid buffers, FIFOs, and Clock Domain Crossing (CDC) interfaces. The testbenches support parameterized testing with different data widths, buffer depths, and operational modes.

## Key Features

- Support for various AXI-style interfaces and buffers
- Parameterized testing via environment variables
- Configurable randomized timing for realistic testing
- Data integrity verification across clock domains and interfaces
- Multi-field and multi-signal variants for complex data paths
- Component statistics collection and analysis
- Comprehensive error detection and reporting
- Advanced sequence generation for thorough testing
- Support for clock domain crossing verification

## Module Components

- [GAXI Buffer](gaxi_buffer.md) - Testbench for basic GAXI buffers
- [GAXI Buffer Configs](gaxi_buffer_configs.md) - Configuration definitions for GAXI testbenches
- [GAXI Buffer Field](gaxi_buffer_field.md) - Testbench for field-based GAXI buffers
- [GAXI Buffer Multi](gaxi_buffer_multi.md) - Testbench for multi-signal GAXI buffers
- [GAXI Buffer Sequence](gaxi_buffer_seq.md) - Sequence generators for GAXI testing
- [GAXI Data Collection](gaxi_data_collect_tb.md) - Testbench for data collection with GAXI interfaces
- [GAXI Enhancements](gaxi_enhancements.md) - Enhanced GAXI master/slave components
- [CDC Handshake](cdc_handshake.md) - Testbench for Clock Domain Crossing handshake verification

## Basic Usage Pattern

All GAXI testbenches follow a similar usage pattern:

```python
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer import GaxiBufferTB

@cocotb.test()
async def test_gaxi_buffer(dut):
    # Create testbench instance
    tb = GaxiBufferTB(
        dut,
        wr_clk=dut.i_clk,
        wr_rstn=dut.i_rst_n,
        rd_clk=dut.i_clk,
        rd_rstn=dut.i_rst_n
    )
    
    # Run simple incremental test
    await tb.simple_incremental_loops(
        count=32,
        delay_key='constrained',
        delay_clks_after=10
    )
```

## Test Configuration

GAXI testbenches are configured via environment variables:

```python
# Environment variables for GAXI testbench configuration
os.environ['TEST_DEPTH'] = '16'           # Buffer depth
os.environ['TEST_WIDTH'] = '32'           # Data width for standard mode
os.environ['TEST_ADDR_WIDTH'] = '32'      # Address width for field mode
os.environ['TEST_CTRL_WIDTH'] = '8'       # Control width for field mode
os.environ['TEST_DATA_WIDTH'] = '32'      # Data width for field mode
os.environ['TEST_MODE'] = 'skid'          # Buffer mode (skid, fifo_mux, etc.)
os.environ['TEST_CLK_WR'] = '10'          # Write clock period
os.environ['TEST_CLK_RD'] = '10'          # Read clock period
```

## Field Configuration

For field-based GAXI testing, field configurations define the packet structure:

```python
FIELD_CONFIGS = {
    'standard': {
        'data': {
            'bits': 32,
            'default': 0,
            'format': 'hex',
            'display_width': 8,
            'active_bits': (31, 0),
            'description': 'Data value'
        }
    },
    'field': {
        'addr': {'bits': 32, 'default': 0, 'format': 'hex'},
        'ctrl': {'bits': 8, 'default': 0, 'format': 'hex'},
        'data0': {'bits': 32, 'default': 0, 'format': 'hex'},
        'data1': {'bits': 32, 'default': 0, 'format': 'hex'}
    }
}
```

## See Also

- [GAXI Components](../../components/gaxi/index.md) - GAXI component building blocks
- [FIFO Testbenches](../fifo/index.md) - FIFO testbench classes (related architecture)
- [AXI4 Testbenches](../axi4/index.md) - AXI4 protocol testbenches

## Navigation

[↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
