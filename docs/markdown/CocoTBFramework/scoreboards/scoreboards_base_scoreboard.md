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

# base_scoreboard.py

Base scoreboard framework providing transaction verification infrastructure for all protocol scoreboards. This module defines the core `BaseScoreboard` class and `ProtocolTransformer` framework used throughout the CocoTBFramework.

## Overview

The base scoreboard system provides:
- **Transaction Queue Management**: Automatic handling of expected vs actual transactions
- **Comparison Framework**: Extensible transaction matching and validation
- **Error Tracking**: Comprehensive error counting and mismatch logging
- **Protocol Transformation**: Framework for cross-protocol transaction conversion
- **Statistics Generation**: Pass/fail rates and performance reporting

## Classes

### BaseScoreboard

Base class for all protocol scoreboards with core verification functionality.

```python
class BaseScoreboard:
    def __init__(self, name, log=None)
```

**Parameters:**
- `name`: Scoreboard name for identification and logging
- `log`: Logger instance for detailed reporting

**Core Attributes:**
- `expected_queue`: Deque of expected transactions
- `actual_queue`: Deque of actual transactions  
- `error_count`: Number of transaction mismatches
- `transaction_count`: Total transactions processed
- `mismatched`: List of (expected, actual) mismatch pairs
- `transformer`: Optional protocol transformer

## Core Methods

### Transaction Management

#### `add_expected(transaction)`
Add transaction to expected queue with optional transformation.

**Parameters:**
- `transaction`: Expected transaction to queue

**Behavior:**
- If transformer is set, transforms transaction before queuing
- Stores transformed transactions in expected queue
- Multiple transformed transactions supported

```python
# Basic usage
scoreboard.add_expected(expected_packet)

# With transformer
scoreboard.set_transformer(apb_to_gaxi_transformer)
scoreboard.add_expected(apb_transaction)  # Automatically transformed to GAXI
```

#### `add_actual(transaction)`
Add actual transaction and trigger automatic comparison.

**Parameters:**
- `transaction`: Actual transaction received

**Behavior:**
- Adds transaction to actual queue
- Increments transaction counter
- Automatically calls `_compare_next()` if both queues have items

```python
# Automatic comparison triggered
scoreboard.add_actual(actual_packet)
```

### Comparison Framework

#### `_compare_next()`
Internal method that compares next available transactions.

**Behavior:**
- Pops one transaction from each queue
- Calls `_compare_transactions()` for validation
- Increments error count on mismatch
- Stores mismatched pairs for analysis
- Calls `_log_mismatch()` on failure

#### `_compare_transactions(expected, actual)` *(Abstract)*
Protocol-specific transaction comparison - must be overridden.

**Parameters:**
- `expected`: Expected transaction
- `actual`: Actual transaction

**Returns:**
- `bool`: True if transactions match, False otherwise

**Implementation Example:**
```python
def _compare_transactions(self, expected, actual):
    """Compare APB transactions based on direction, address, and data"""
    if not isinstance(expected, APBPacket) or not isinstance(actual, APBPacket):
        return False
    
    return expected == actual  # Use packet's __eq__ method
```

#### `_log_mismatch(expected, actual)`
Log detailed mismatch information - can be overridden for enhanced logging.

**Parameters:**
- `expected`: Expected transaction
- `actual`: Actual transaction

**Default Behavior:**
- Logs basic mismatch with transaction strings
- Protocol-specific implementations provide detailed field comparison

### Reporting and Statistics

#### `report()`
Generate comprehensive scoreboard report.

**Returns:**
- `int`: Total error count (mismatches + leftover transactions)

**Report Contents:**
- Leftover expected transactions (not received)
- Leftover actual transactions (without matching expected)
- Total transaction count and error summary

```python
error_count = scoreboard.report()
if error_count == 0:
    print("All transactions matched successfully")
```

#### `result()`
Calculate pass rate as success ratio.

**Returns:**
- `float`: Pass rate from 0.0 to 1.0

**Calculation:**
- Total = transaction_count + len(expected_queue)
- Failures = error_count + len(expected_queue) + len(actual_queue)
- Result = (total - failures) / total

```python
pass_rate = scoreboard.result()
print(f"Verification pass rate: {pass_rate:.2%}")
```

### Utility Methods

#### `set_transformer(transformer)`
Set protocol transformer for expected transactions.

**Parameters:**
- `transformer`: ProtocolTransformer instance

```python
transformer = APBtoGAXITransformer(gaxi_field_config, GAXIPacket)
scoreboard.set_transformer(transformer)
```

#### `clear()`
Reset scoreboard state for new test phase.

**Behavior:**
- Clears all transaction queues
- Resets error and transaction counters
- Preserves transformer configuration

```python
# Reset between test phases
scoreboard.clear()
```

## Protocol Transformer Framework

### ProtocolTransformer

Base class for converting transactions between different protocols.

```python
class ProtocolTransformer:
    def __init__(self, source_type, target_type, log=None)
```

**Parameters:**
- `source_type`: Source protocol name (e.g., "APB")
- `target_type`: Target protocol name (e.g., "GAXI")
- `log`: Logger instance

**Statistics:**
- `num_transformations`: Successful transformation count
- `num_failures`: Failed transformation count

### Core Methods

#### `transform(transaction)` *(Abstract)*
Transform transaction from source to target protocol.

**Parameters:**
- `transaction`: Source transaction to transform

**Returns:**
- `List`: Target transactions (can be empty if transformation fails)

**Implementation Example:**
```python
def transform(self, apb_transaction):
    """Transform APB to GAXI transaction"""
    gaxi_packet = GAXIPacket(self.field_config)
    
    # Map fields
    gaxi_packet.addr = apb_transaction.paddr
    gaxi_packet.data = apb_transaction.pwdata if apb_transaction.direction == 'WRITE' else apb_transaction.prdata
    gaxi_packet.cmd = 1 if apb_transaction.direction == 'WRITE' else 0
    
    return [gaxi_packet]
```

#### `try_transform(transaction)`
Safe transformation with error handling.

**Parameters:**
- `transaction`: Source transaction to transform

**Returns:**
- `List`: Target transactions (empty if transformation fails)

**Behavior:**
- Wraps `transform()` with exception handling
- Updates success/failure statistics
- Logs transformation errors

```python
# Safe transformation
results = transformer.try_transform(source_transaction)
if results:
    print(f"Transformation successful: {len(results)} target transactions")
```

#### `report()`
Generate transformer statistics report.

**Returns:**
- `str`: Report with transformation statistics

```python
print(transformer.report())
# Output:
# APB to GAXI Transformer Report
#   Successful transformations: 150
#   Failed transformations: 3
```

## Usage Patterns

### Basic Scoreboard Usage

```python
from CocoTBFramework.scoreboards.base_scoreboard import BaseScoreboard

class CustomScoreboard(BaseScoreboard):
    def _compare_transactions(self, expected, actual):
        # Implement protocol-specific comparison
        return expected.key_field == actual.key_field
    
    def _log_mismatch(self, expected, actual):
        # Enhanced mismatch logging
        if self.log:
            self.log.error(f"Mismatch in {self.name}:")
            self.log.error(f"  Expected: {expected}")
            self.log.error(f"  Actual: {actual}")

# Usage
scoreboard = CustomScoreboard("TestScoreboard", log=logger)
scoreboard.add_expected(expected_transaction)
scoreboard.add_actual(actual_transaction)
error_count = scoreboard.report()
```

### Protocol Transformation

```python
from CocoTBFramework.scoreboards.base_scoreboard import ProtocolTransformer

class APBtoGAXITransformer(ProtocolTransformer):
    def __init__(self, gaxi_field_config, log=None):
        super().__init__("APB", "GAXI", log)
        self.field_config = gaxi_field_config
    
    def transform(self, apb_transaction):
        # Create GAXI packet
        gaxi_packet = GAXIPacket(self.field_config)
        
        # Map protocol fields
        gaxi_packet.addr = apb_transaction.paddr
        gaxi_packet.cmd = 1 if apb_transaction.direction == 'WRITE' else 0
        
        if apb_transaction.direction == 'WRITE':
            gaxi_packet.data = apb_transaction.pwdata
        else:
            gaxi_packet.data = apb_transaction.prdata
            
        return [gaxi_packet]

# Usage with scoreboard
transformer = APBtoGAXITransformer(gaxi_field_config, log=logger)
scoreboard.set_transformer(transformer)

# APB transactions automatically converted to GAXI for comparison
scoreboard.add_expected(apb_transaction)  # Transformed to GAXI
scoreboard.add_actual(gaxi_packet)        # Direct GAXI comparison
```

### Multi-Protocol Verification

```python
# Create cross-protocol verification system
apb_to_gaxi = APBtoGAXITransformer(gaxi_config, log=logger)
gaxi_scoreboard = GAXIScoreboard("Bridge", gaxi_config, log=logger)
gaxi_scoreboard.set_transformer(apb_to_gaxi)

# Verify APB input produces correct GAXI output
gaxi_scoreboard.add_expected(apb_input)    # Transformed to GAXI
gaxi_scoreboard.add_actual(gaxi_output)    # Direct comparison

# Generate verification results
errors = gaxi_scoreboard.report()
pass_rate = gaxi_scoreboard.result()
```

## Best Practices

### Error Handling
- Always provide logger instances for detailed debugging
- Override `_log_mismatch()` for protocol-specific error analysis
- Use `try_transform()` for robust transformation

### Performance Optimization
- Clear scoreboards between test phases to manage memory
- Use deque operations for efficient queue management
- Monitor transaction counts in long-running tests

### Extensibility
- Inherit from `BaseScoreboard` for protocol-specific implementations
- Create custom transformers for complex protocol conversions
- Use composition pattern for multi-stage transformation pipelines

## Integration Points

### Monitor Integration
```python
# Connect monitor callbacks to scoreboard
def on_transaction_received(packet):
    scoreboard.add_actual(packet)

monitor.add_callback(on_transaction_received)
```

### Memory Model Integration
```python
# Memory-backed verification
class MemoryScoreboard(BaseScoreboard):
    def __init__(self, name, memory_model, log=None):
        super().__init__(name, log)
        self.memory = memory_model
    
    def _compare_transactions(self, expected, actual):
        # Compare against memory contents
        stored_data = self.memory.read(actual.addr)
        return stored_data == actual.data
```

The base scoreboard framework provides a robust foundation for verification across all protocols in the CocoTBFramework, enabling both simple transaction checking and complex cross-protocol verification scenarios.