# FIFO Testbenches

## Overview

The `tbclasses/fifo` module provides testbench classes for verifying different types of FIFO (First-In-First-Out) buffer implementations. These testbenches build upon the FIFO components to provide comprehensive verification environments for synchronous, asynchronous, and specialized FIFO designs. The test classes support parameterized testing with different data widths, buffer depths, and operational modes.

## Key Features

- Support for various FIFO architectures (synchronous, skid buffer, etc.)
- Parameterized testing via environment variables
- Configurable randomized timing for realistic testing
- Data integrity verification across interfaces
- Performance and capacity metrics collection
- Support for different FIFO operational modes (flop, mux, field)
- Comprehensive error detection and reporting
- Multi-field data path support
- Test isolation for better debug capabilities

## Module Components

- [FIFO Buffer](fifo_buffer.md) - Testbench for basic FIFO buffers
- [FIFO Buffer Configs](fifo_buffer_configs.md) - Configuration definitions for FIFO testbenches
- [FIFO Buffer Field](fifo_buffer_field.md) - Testbench for field-based FIFO buffers
- [FIFO Buffer Multi](fifo_buffer_multi.md) - Testbench for multi-signal FIFO buffers
- [FIFO Data Collection](fifo_data_collect_tb.md) - Testbench for data collection with FIFO interfaces

## Basic Usage Pattern

All FIFO testbenches follow a similar usage pattern:

```python
from CocoTBFramework.tbclasses.fifo.fifo_buffer import FifoBufferTB

@cocotb.test()
async def test_fifo_buffer(dut):
    # Create testbench instance
    tb = FifoBufferTB(
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
    
    # Run stress test with random patterns
    await tb.stress_test_with_random_patterns(
        count=100,
        delay_key='constrained'
    )
```

## Test Configuration

FIFO testbenches are configured via environment variables:

```python
# Environment variables for FIFO testbench configuration
os.environ['TEST_DEPTH'] = '16'       # FIFO depth
os.environ['TEST_DATA_WIDTH'] = '32'  # Data width
os.environ['TEST_MODE'] = 'fifo_mux'  # FIFO mode
os.environ['TEST_KIND'] = 'sync'      # FIFO kind (sync/async)
os.environ['TEST_CLK_WR'] = '10'      # Write clock period
os.environ['TEST_CLK_RD'] = '10'      # Read clock period
```

## Field Configuration

For field-based FIFO testing, field configurations define the packet structure:

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

- [FIFO Components](../../components/fifo/index.md) - FIFO component building blocks
- [GAXI Testbenches](../gaxi/index.md) - Generic AXI testbenches (related protocol)
- [Common Testbenches](../common/index.md) - Common digital logic test classes

## Navigation

[↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
