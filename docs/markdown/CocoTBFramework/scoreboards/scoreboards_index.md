# Scoreboards Index

This directory contains scoreboard implementations for verifying transactions across different protocols in the CocoTBFramework. Scoreboards provide automated comparison between expected and actual transactions, protocol compliance checking, and comprehensive reporting.

## Overview
- [**Overview**](overview.md) - Complete overview of the scoreboards directory and verification architecture

## Core Documentation

### Base Framework
- [**base_scoreboard.py**](base_scoreboard.md) - Base scoreboard class and protocol transformer framework providing common functionality for all scoreboards

### Protocol-Specific Scoreboards
- [**apb_scoreboard.py**](apb_scoreboard.md) - APB (Advanced Peripheral Bus) transaction verification with multi-slave support
- [**axi4_scoreboard.py**](axi4_scoreboard.md) - AXI4 protocol transaction verification with ID tracking and channel separation
- [**fifo_scoreboard.py**](fifo_scoreboard.md) - FIFO protocol transaction verification with memory integration
- [**gaxi_scoreboard.py**](gaxi_scoreboard.md) - GAXI (Generic AXI) protocol transaction verification with field-based comparison

### Cross-Protocol Verification
- [**apb_gaxi_scoreboard.py**](apb_gaxi_scoreboard.md) - APB-GAXI protocol bridge verification with three-phase matching
- [**apb_gaxi_transformer.py**](apb_gaxi_transformer.md) - Bidirectional protocol transformation between APB and GAXI

## Quick Start

### Basic Scoreboard Usage
```python
from CocoTBFramework.scoreboards.gaxi_scoreboard import GAXIScoreboard

# Create scoreboard
scoreboard = GAXIScoreboard("TestScoreboard", field_config, log=logger)

# Add expected and actual transactions
scoreboard.add_expected(expected_packet)
scoreboard.add_actual(actual_packet)

# Generate report
error_count = scoreboard.report()
success_rate = scoreboard.result()
```

### Cross-Protocol Verification
```python
from CocoTBFramework.scoreboards.apb_gaxi_scoreboard import APBGAXIScoreboard

# Create cross-protocol scoreboard
scoreboard = APBGAXIScoreboard("APB_GAXI_Bridge", log=logger)

# Add transactions from both protocols
scoreboard.add_apb_transaction(apb_transaction)
scoreboard.add_gaxi_command(gaxi_command)
scoreboard.add_gaxi_response(gaxi_response)

# Generate comprehensive report
report = scoreboard.report()
stats = scoreboard.get_stats()
```

### Multi-Slave APB Verification
```python
from CocoTBFramework.scoreboards.apb_scoreboard import APBMultiSlaveScoreboard

# Create multi-slave scoreboard
scoreboard = APBMultiSlaveScoreboard("MultiSlave", num_slaves=4, log=logger)

# Set custom address mapping
addr_map = [
    (0x0000, 0x0FFF),  # Slave 0
    (0x1000, 0x1FFF),  # Slave 1
    (0x2000, 0x2FFF),  # Slave 2
    (0x3000, 0x3FFF),  # Slave 3
]
scoreboard.set_address_map(addr_map)

# Route transactions automatically
scoreboard.add_master_transaction(transaction, master_id=0)
```

## Architecture Overview

### Scoreboard Hierarchy
```
┌─────────────────────────────────────────────────────────┐
│                 Protocol Scoreboards                   │
│   ┌─────────────┐ ┌─────────────┐ ┌─────────────┐     │
│   │     APB     │ │    GAXI     │ │    FIFO     │     │
│   │ Scoreboard  │ │ Scoreboard  │ │ Scoreboard  │     │
│   └─────────────┘ └─────────────┘ └─────────────┘     │
│   ┌─────────────┐ ┌─────────────┐ ┌─────────────┐     │
│   │    AXI4     │ │ APB-GAXI    │ │   Future    │     │
│   │ Scoreboard  │ │ Scoreboard  │ │ Scoreboards │     │
│   └─────────────┘ └─────────────┘ └─────────────┘     │
└─────────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────────┐
│                 Cross-Protocol Support                 │
│   ┌─────────────┐ ┌─────────────┐ ┌─────────────┐     │
│   │ Protocol    │ │ Transform   │ │ Memory      │     │
│   │Transformers │ │ Scoreboard  │ │ Adapters    │     │
│   └─────────────┘ └─────────────┘ └─────────────┘     │
└─────────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────────┐
│                   Base Framework                       │
│   ┌─────────────┐ ┌─────────────┐ ┌─────────────┐     │
│   │    Base     │ │ Transaction │ │ Statistics  │     │
│   │ Scoreboard  │ │   Queuing   │ │& Reporting  │     │
│   └─────────────┘ └─────────────┘ └─────────────┘     │
└─────────────────────────────────────────────────────────┘
```

## Key Features

### Base Scoreboard Framework
- **Transaction Queuing**: Automatic queueing and matching of expected vs actual transactions
- **Error Tracking**: Comprehensive error counting and mismatch logging
- **Protocol Transformers**: Support for cross-protocol transaction conversion
- **Statistics Reporting**: Pass/fail rates and detailed transaction statistics

### Protocol-Specific Features

#### APB Scoreboard
- **Multi-slave Support**: Route transactions to correct slave scoreboards based on address ranges
- **Address Mapping**: Configurable address ranges for automatic slave selection
- **Direction Handling**: Separate processing for read and write transactions
- **Enhanced Logging**: Detailed field-by-field mismatch reporting

#### AXI4 Scoreboard
- **ID-based Tracking**: Track transactions by AXI4 ID fields with separate queues per ID
- **Read/Write Separation**: Independent queues for read and write channels
- **Protocol Compliance**: Check for AXI4 protocol violations and timing constraints
- **Monitor Integration**: Direct connection to AXI4 monitor components

#### FIFO Scoreboard
- **Memory Integration**: Built-in memory model adapter for data verification
- **Field Configuration**: Flexible field mapping and comparison using FieldConfig
- **Packet Format Support**: Native support for FIFO packet classes

#### GAXI Scoreboard
- **Field-based Comparison**: Uses FieldConfig for flexible packet structure comparison
- **Memory Adaptation**: Integration with memory models for transaction verification
- **Transform Support**: Cross-protocol transformation capabilities

### Cross-Protocol Support
- **APB-GAXI Bridge**: Specialized scoreboard for verifying protocol bridges with three-phase matching
- **Bidirectional Transformation**: Convert between APB and GAXI formats with timing preservation
- **Timing Analysis**: Track transformation latency and performance metrics
- **Response Matching**: Proper handling of both read and write responses

## Advanced Usage

### Custom Protocol Transformers
```python
from CocoTBFramework.scoreboards.base_scoreboard import ProtocolTransformer

class CustomTransformer(ProtocolTransformer):
    def __init__(self, source_type, target_type, log=None):
        super().__init__(source_type, target_type, log)
    
    def transform(self, transaction):
        # Implement custom transformation logic
        return [transformed_transaction]

# Use with scoreboard
scoreboard.set_transformer(CustomTransformer("Protocol1", "Protocol2"))
```

### Memory Model Integration
```python
from CocoTBFramework.scoreboards.fifo_scoreboard import MemoryAdapter
from CocoTBFramework.components.shared.memory_model import MemoryModel

# Create memory model and adapter
memory = MemoryModel(size=1024*1024, log=logger)
adapter = MemoryAdapter(memory, field_map={'addr': 'address', 'data': 'data'})

# Use with scoreboard for automatic verification
scoreboard.set_memory_adapter(adapter)
```

### Statistics and Reporting
```python
# Get comprehensive statistics
stats = scoreboard.get_stats()
print(f"Pass Rate: {stats['pass_rate']}%")
print(f"Total Transactions: {stats['total_transactions']}")
print(f"Mismatches: {stats['mismatch_count']}")

# Generate detailed report
report = scoreboard.generate_detailed_report()
with open("verification_report.html", "w") as f:
    f.write(report)
```

## Integration Patterns

### With Monitor Components
```python
# Connect monitors to scoreboards automatically
master_monitor.add_callback(scoreboard.add_expected)
slave_monitor.add_callback(scoreboard.add_actual)

# Or manually add transactions
for packet in master_transactions:
    scoreboard.add_expected(packet)

for packet in slave_responses:
    scoreboard.add_actual(packet)
```

### With Test Frameworks
```python
@cocotb.test()
async def test_with_scoreboard(dut):
    # Create scoreboard
    scoreboard = GAXIScoreboard("TestSB", field_config, log=logger)
    
    # Run test with automatic transaction capture
    await run_test_sequence(dut, scoreboard)
    
    # Verify results
    error_count = scoreboard.report()
    assert error_count == 0, f"Scoreboard reported {error_count} errors"
    
    # Get pass/fail status
    success = scoreboard.result()
    assert success > 0.95, f"Pass rate too low: {success}"
```

## Best Practices

### Scoreboard Setup
1. **Choose appropriate scoreboard type** based on protocol being verified
2. **Configure field mappings** for packet comparison
3. **Set up memory adapters** when verifying memory-mapped interfaces
4. **Configure timeout values** for transaction matching

### Error Handling
- Always provide logger instances for detailed error reporting
- Use `clear()` method to reset scoreboards between test phases
- Check both `report()` and `result()` methods for comprehensive analysis
- Review field-by-field mismatch reports for debugging

### Performance Optimization
- Use appropriate transformer configurations for cross-protocol verification
- Clear transaction queues periodically in long-running tests
- Monitor memory usage with large transaction volumes
- Configure appropriate matching timeout values

### Debugging Support
- Enable detailed logging for mismatch analysis
- Use formatted output methods for transaction comparison
- Leverage built-in statistics for performance analysis
- Generate HTML reports for comprehensive analysis

## Navigation
- [**Back to CocoTBFramework**](../index.md) - Return to main framework index