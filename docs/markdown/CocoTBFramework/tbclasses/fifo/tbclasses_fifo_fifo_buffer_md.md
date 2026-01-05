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

# fifo_buffer.py

Basic FIFO buffer testbench with modern infrastructure and simplified instantiation. This is the foundational testbench for single-signal FIFO verification.

## Overview

The `FifoBufferTB` class provides a comprehensive yet straightforward testbench for basic FIFO verification. It implements essential FIFO testing patterns including basic read/write operations, randomized traffic, and data integrity verification. This testbench serves as the entry point for FIFO verification and demonstrates core CocoTBFramework patterns.

## Key Features

- **Single Signal Interface**: Simple data/valid/ready interface pattern
- **FlexConfigGen Integration**: Modern randomization framework
- **Clock Domain Support**: Both synchronous and asynchronous FIFO testing
- **Memory Modeling**: Reference model for data integrity verification
- **Comprehensive Monitoring**: Full transaction tracking and analysis

## Class Definition

```python
class FifoBufferTB(TBBase):
    """Testbench for FIFO buffer components using FlexConfigGen only for randomization"""
```

## Constructor Parameters

```python
def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None):
```

### Parameters
- **dut**: Device Under Test (DUT) object
- **wr_clk**: Write clock signal (optional, auto-detected if None)
- **wr_rstn**: Write reset signal (optional, auto-detected if None)  
- **rd_clk**: Read clock signal (optional, auto-detected if None)
- **rd_rstn**: Read reset signal (optional, auto-detected if None)

## Environment Configuration

The testbench is configured through environment variables:

### Core Parameters
- `TEST_DEPTH`: FIFO depth (default: 0 - auto-detected)
- `TEST_DATA_WIDTH`: Data width in bits (default: 0 - auto-detected)
- `TEST_MODE`: Operation mode ('fifo_mux', 'fifo_simple') (default: 'fifo_mux')
- `TEST_KIND`: Clock domain type ('sync', 'async') (default: 'sync')

### Clock Configuration
- `TEST_CLK_WR`: Write clock period in ns (default: 10)
- `TEST_CLK_RD`: Read clock period in ns (default: 10)

### Test Control
- `SEED`: Random seed for reproducible tests (default: 12345)

## Component Architecture

### Core Components

**Write Side:**
- `FIFOMaster` - Drives write transactions
- Write monitor - Captures write-side activity

**Read Side:**
- `FIFOSlave` - Handles read operations
- Read monitor - Captures read-side activity

**Infrastructure:**
- `MemoryModel` - Reference model for data verification
- `FlexConfigGen` - Randomization profiles and generators

### Signal Interface

Standard FIFO interface:
- `write`: Write enable
- `data`: Write data
- `full`: FIFO full flag
- `read`: Read enable  
- `q`: Read data
- `empty`: FIFO empty flag

## Test Methods

### Basic Traffic Tests

#### `test_basic_traffic(packet_count=100)`
Basic read/write traffic with simple patterns.

**Purpose**: Verify fundamental FIFO functionality
**Pattern**: Sequential write followed by sequential read
**Verification**: Data integrity and ordering

```python
await tb.test_basic_traffic(packet_count=50)
```

#### `test_randomized_traffic(packet_count=500, profile='balanced')`
Randomized traffic patterns using FlexConfigGen profiles.

**Purpose**: Stress test with realistic traffic patterns
**Profiles**: 'conservative', 'moderate', 'aggressive', 'balanced'
**Verification**: Random data patterns with comprehensive checking

```python
await tb.test_randomized_traffic(packet_count=200, profile='aggressive')
```

### Stress Tests

#### `test_back_to_back(packet_count=1000)`
Continuous back-to-back operations without gaps.

**Purpose**: Maximum throughput testing
**Pattern**: Continuous write until full, then continuous read until empty
**Verification**: Maximum rate data integrity

#### `test_mixed_traffic(packet_count=500)`
Mixed read/write operations with random timing.

**Purpose**: Realistic operation pattern testing
**Pattern**: Interleaved read/write with random delays
**Verification**: Complex traffic pattern handling

### Boundary Tests

#### `test_empty_full_conditions()`
Tests FIFO empty and full boundary conditions.

**Purpose**: Edge case verification
**Pattern**: Fill to capacity, empty completely, verify flags
**Verification**: Proper flag behavior and data integrity

#### `test_clock_domain_crossing()`
Tests asynchronous FIFO operation (if TEST_KIND='async').

**Purpose**: Cross-clock domain verification
**Pattern**: Independent clock rates with phase variations
**Verification**: Data integrity across clock domains

## Usage Examples

### Basic Test Setup

```python
import cocotb
from CocoTBFramework.tbclasses.fifo.fifo_buffer import FifoBufferTB

@cocotb.test()
async def test_basic_fifo(dut):
    tb = FifoBufferTB(dut)
    await tb.initialize()
    
    # Basic functionality test
    await tb.test_basic_traffic(packet_count=100)
    
    # Verify results
    tb.verify_results()
```

### Advanced Test Configuration

```python
import os
import cocotb
from CocoTBFramework.tbclasses.fifo.fifo_buffer import FifoBufferTB

@cocotb.test()
async def test_advanced_fifo(dut):
    # Configure environment
    os.environ['TEST_DATA_WIDTH'] = '32'
    os.environ['TEST_DEPTH'] = '16' 
    os.environ['TEST_MODE'] = 'fifo_mux'
    os.environ['SEED'] = '54321'
    
    tb = FifoBufferTB(dut)
    await tb.initialize()
    
    # Multiple test sequences
    await tb.test_basic_traffic(packet_count=50)
    await tb.test_randomized_traffic(packet_count=200, profile='moderate')
    await tb.test_back_to_back(packet_count=100)
    await tb.test_mixed_traffic(packet_count=150)
    
    # Boundary condition testing
    await tb.test_empty_full_conditions()
    
    tb.verify_results()
```

### Asynchronous FIFO Testing

```python
@cocotb.test()
async def test_async_fifo(dut):
    # Configure for async operation
    os.environ['TEST_KIND'] = 'async'
    os.environ['TEST_CLK_WR'] = '10'  # 100 MHz write clock
    os.environ['TEST_CLK_RD'] = '15'  # ~67 MHz read clock
    
    tb = FifoBufferTB(dut)
    await tb.initialize()
    
    # Clock domain crossing tests
    await tb.test_clock_domain_crossing()
    await tb.test_randomized_traffic(packet_count=300, profile='aggressive')
    
    tb.verify_results()
```

## Randomization Profiles

### Conservative Profile
- Low-frequency operations
- Predictable patterns
- Minimal stress on timing

### Moderate Profile  
- Balanced operation rate
- Mixed predictable and random patterns
- Good for general functionality testing

### Aggressive Profile
- High-frequency operations
- Maximum stress patterns
- Rapid-fire back-to-back operations

### Balanced Profile
- Optimized mix of all patterns
- Comprehensive coverage
- Recommended for thorough testing

## Verification and Debugging

### Automatic Verification

The testbench includes comprehensive automatic verification:
- **Data Integrity**: Every packet verified end-to-end
- **Order Verification**: FIFO ordering maintained
- **Flag Verification**: Empty/full flags verified
- **Protocol Compliance**: Interface timing verified

### Debug Features

- **Transaction Logging**: Complete packet trace
- **Statistics Collection**: Performance metrics
- **Error Reporting**: Detailed error analysis
- **Memory Model**: Reference for data tracking

### Common Issues and Solutions

**Issue**: Timeout during test
**Solution**: Check clock configuration and TEST_CLK_* settings

**Issue**: Data corruption detected
**Solution**: Verify DUT signal connections and timing

**Issue**: Performance lower than expected  
**Solution**: Review randomization profile and adjust for higher throughput

## Integration with Other Testbenches

This basic testbench serves as the foundation for more complex FIFO testbenches:

- **fifo_buffer_field.py**: Extends with multi-field support
- **fifo_buffer_multi.py**: Extends with multi-signal support
- **fifo_data_collect_tb.py**: Extends with multi-channel arbitration

The common patterns and infrastructure ensure easy migration and reuse of test methodologies across the FIFO testbench suite.