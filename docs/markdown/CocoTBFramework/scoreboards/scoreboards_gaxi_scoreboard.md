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

# gaxi_scoreboard.py

GAXI (Generic AXI) protocol scoreboard implementation for verifying GAXI transactions with modern field configuration support and protocol transformation capabilities. This module provides comprehensive verification for GAXI-based communication systems.

## Overview

The GAXI scoreboard system provides:
- **Modern Field Configuration**: Full integration with updated FieldConfig and Packet classes
- **Flexible Packet Handling**: Support for both legacy and modern packet formats
- **Protocol Transformation**: Enhanced cross-protocol verification capabilities
- **Memory Model Integration**: Built-in memory adapter for data consistency checking
- **Transform Scoreboards**: Specialized scoreboards for protocol conversion verification

## Classes

### GAXIScoreboard

Core GAXI transaction verification with modern architecture support.

```python
class GAXIScoreboard(BaseScoreboard):
    def __init__(self, name, field_config, log=None)
```

**Parameters:**
- `name`: Scoreboard name for identification
- `field_config`: Field configuration (FieldConfig object or dictionary)
- `log`: Logger instance for detailed reporting

**Modern Features:**
- Automatic FieldConfig validation and conversion
- Support for updated Packet class with fields dictionary
- Enhanced field-by-field comparison logging
- Backward compatibility with legacy packet formats

### Field Configuration Handling

The scoreboard automatically handles different field configuration formats:

```python
# Dictionary format (automatically converted)
field_dict = {'data': 32, 'addr': 32, 'cmd': 1}
scoreboard = GAXIScoreboard("Test", field_dict, log=logger)

# FieldConfig object (used directly)
field_config = FieldConfig.validate_and_create(field_dict)
scoreboard = GAXIScoreboard("Test", field_config, log=logger)
```

## Core Methods

### Transaction Comparison

#### `_compare_transactions(expected, actual)`
Compare GAXI packets using modern packet equality methods.

**Parameters:**
- `expected`: Expected GAXI transaction (GAXIPacket)
- `actual`: Actual GAXI transaction (GAXIPacket)

**Returns:**
- `bool`: True if packets match, False otherwise

**Modern Comparison Logic:**
- Validates transaction types (must be GAXIPacket instances)
- Uses Packet class `__eq__` method which automatically skips timing fields
- Compares all configured fields using field_config
- Handles both legacy and modern packet formats

```python
# Automatic comparison with timing field exclusion
scoreboard.add_expected(expected_packet)  # start_time, end_time ignored
scoreboard.add_actual(actual_packet)      # Only functional fields compared
```

#### `_log_mismatch(expected, actual)`
Enhanced mismatch logging with modern packet format support.

**Parameters:**
- `expected`: Expected GAXI packet
- `actual`: Actual GAXI packet

**Enhanced Logging Features:**
- Uses packet's `formatted(compact=True)` method for readable output
- Automatic detection of packet format (modern vs legacy)
- Field-by-field comparison using FieldConfig
- Hexadecimal display for clear value comparison

```python
# Example modern mismatch log output:
# GAXI Packet mismatch:
#   Expected: addr=0x1000, data=0xDEADBEEF, cmd=1
#   Actual:   addr=0x1000, data=0xBEEFDEAD, cmd=1
#   Field 'data' mismatch: expected=0xDEADBEEF, actual=0xBEEFDEAD
```

## Advanced Scoreboards

### TransformScoreboard

Specialized scoreboard for protocol transformation verification.

```python
class TransformScoreboard(BaseScoreboard):
    def __init__(self, name, transformer, target_scoreboard, log=None)
```

**Parameters:**
- `name`: Scoreboard name
- `transformer`: Protocol transformer instance
- `target_scoreboard`: Target scoreboard for verification
- `log`: Logger instance

**Transform Workflow:**
1. Source transactions added via `add_expected()`
2. Transformer converts source to target protocol
3. Converted transactions forwarded to target scoreboard
4. Actual transactions added directly to target scoreboard
5. Verification performed in target protocol domain

```python
# Cross-protocol verification setup
apb_to_gaxi = APBtoGAXITransformer(gaxi_field_config)
gaxi_scoreboard = GAXIScoreboard("Target", gaxi_field_config)
transform_scoreboard = TransformScoreboard("Bridge", apb_to_gaxi, gaxi_scoreboard)

# APB input automatically transformed for GAXI comparison
transform_scoreboard.add_expected(apb_transaction)  # Transformed to GAXI
transform_scoreboard.add_actual(gaxi_packet)        # Direct comparison
```

### Memory Integration

### GAXItoMemoryAdapter

Adapter for memory model integration with GAXI packets.

```python
class GAXItoMemoryAdapter:
    def __init__(self, memory_model, field_map=None, log=None)
```

**Parameters:**
- `memory_model`: Memory model instance for data storage
- `field_map`: Field mapping configuration for memory operations
- `log`: Logger instance

**Default Field Mapping:**
- `'addr'`: Address field for memory operations
- `'data'`: Data field for read/write operations
- `'strb'`: Strobe field for byte enable operations

#### Memory Operations

##### `write_to_memory(packet)`
Write GAXI packet data to memory model.

**Parameters:**
- `packet`: GAXI packet containing write data

**Behavior:**
- Extracts address and data from packet fields
- Handles strobe-based byte enables if present
- Updates memory model with packet data
- Logs write operation for debugging

```python
# Memory write with strobe support
adapter = GAXItoMemoryAdapter(memory_model)
write_packet = create_gaxi_write(addr=0x1000, data=0xDEADBEEF, strb=0xF)
adapter.write_to_memory(write_packet)
```

##### `read_from_memory(packet)`
Verify read packet data against memory contents.

**Parameters:**
- `packet`: GAXI packet containing expected read data

**Returns:**
- `bool`: True if packet data matches memory contents

**Verification Process:**
- Extracts address from packet
- Reads current memory contents at address
- Compares memory data with packet data field
- Returns match status for verification

```python
# Memory read verification
read_packet = create_gaxi_read(addr=0x1000, data=0xDEADBEEF)
match = adapter.read_from_memory(read_packet)
if not match:
    print("Memory read data mismatch")
```

## Usage Examples

### Basic GAXI Verification

```python
from CocoTBFramework.scoreboards.gaxi_scoreboard import GAXIScoreboard
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket
from CocoTBFramework.components.shared.field_config import FieldConfig

# Modern field configuration
field_config = FieldConfig.from_dict({
    'addr': 32,
    'data': 32,
    'cmd': 1,
    'strb': 4
})

# Create scoreboard with modern field config
scoreboard = GAXIScoreboard("GAXI_Test", field_config, log=logger)

# Create test packets using modern Packet class
expected = GAXIPacket(field_config)
expected.fields['addr'] = 0x1000
expected.fields['data'] = 0xDEADBEEF
expected.fields['cmd'] = 1  # Write
expected.fields['strb'] = 0xF

actual = GAXIPacket(field_config)
actual.fields['addr'] = 0x1000
actual.fields['data'] = 0xDEADBEEF
actual.fields['cmd'] = 1
actual.fields['strb'] = 0xF

# Verify transactions (timing fields automatically ignored)
scoreboard.add_expected(expected)
scoreboard.add_actual(actual)

# Check results
error_count = scoreboard.report()
pass_rate = scoreboard.result()
print(f"GAXI Verification: {'PASS' if error_count == 0 else 'FAIL'} ({pass_rate:.2%})")
```

### Cross-Protocol Transformation Verification

```python
from CocoTBFramework.scoreboards.gaxi_scoreboard import TransformScoreboard
from CocoTBFramework.scoreboards.apb_gaxi_transformer import APBtoGAXITransformer
from CocoTBFramework.components.apb.apb_packet import APBPacket

# Create transformation pipeline
transformer = APBtoGAXITransformer(gaxi_field_config, GAXIPacket, log=logger)
target_scoreboard = GAXIScoreboard("GAXI_Target", gaxi_field_config, log=logger)
bridge_scoreboard = TransformScoreboard("APB_GAXI_Bridge", transformer, target_scoreboard, log=logger)

# Create APB input transaction
apb_transaction = APBPacket()
apb_transaction.direction = 'WRITE'
apb_transaction.paddr = 0x2000
apb_transaction.pwdata = 0x12345678
apb_transaction.pstrb = 0xF

# Create expected GAXI output (from DUT)
gaxi_output = GAXIPacket(gaxi_field_config)
gaxi_output.fields['addr'] = 0x2000
gaxi_output.fields['data'] = 0x12345678
gaxi_output.fields['cmd'] = 1
gaxi_output.fields['strb'] = 0xF

# Verify transformation
bridge_scoreboard.add_expected(apb_transaction)  # Auto-transformed to GAXI
bridge_scoreboard.add_actual(gaxi_output)        # Direct GAXI comparison

# Analysis
errors = bridge_scoreboard.report()
if errors == 0:
    print("Bridge transformation verified successfully")
else:
    print(f"Bridge verification failed: {errors} errors")
```

### Memory-Backed GAXI System Verification

```python
from CocoTBFramework.scoreboards.gaxi_scoreboard import GAXItoMemoryAdapter
from CocoTBFramework.components.shared.memory_model import MemoryModel

# Create memory system
memory = MemoryModel(size=1024*1024, log=logger)
field_map = {
    'addr': 'addr',
    'data': 'data',
    'strb': 'strb'
}
adapter = GAXItoMemoryAdapter(memory, field_map, log=logger)

# Create memory-integrated verification environment
class MemoryGAXIScoreboard(GAXIScoreboard):
    def __init__(self, name, field_config, memory_adapter, log=None):
        super().__init__(name, field_config, log)
        self.memory_adapter = memory_adapter
    
    def add_expected(self, packet):
        # For write transactions, update memory
        if packet.fields.get('cmd') == 1:  # Write
            self.memory_adapter.write_to_memory(packet)
        super().add_expected(packet)
    
    def _compare_transactions(self, expected, actual):
        # Standard comparison
        basic_match = super()._compare_transactions(expected, actual)
        
        # Additional memory consistency check for reads
        if actual.fields.get('cmd') == 0:  # Read
            memory_match = self.memory_adapter.read_from_memory(actual)
            if not memory_match and self.log:
                self.log.error("Memory consistency check failed for read transaction")
            return basic_match and memory_match
        
        return basic_match

# Usage
memory_scoreboard = MemoryGAXIScoreboard("MemorySystem", gaxi_field_config, adapter, log=logger)

# Test write-then-read sequence
write_packet = create_gaxi_write(addr=0x1000, data=0xABCDEF00)
read_packet = create_gaxi_read(addr=0x1000, data=0xABCDEF00)

memory_scoreboard.add_expected(write_packet)  # Updates memory
memory_scoreboard.add_expected(read_packet)   # Verified against memory

# ... add actual transactions from DUT ...
```

### Advanced Multi-Channel Verification

```python
# Multi-channel GAXI verification system
async def test_multi_channel_gaxi():
    # Define multi-channel field configuration
    field_config = FieldConfig.from_dict({
        'addr': 32,
        'data': 64,
        'cmd': 1,
        'strb': 8,
        'channel': 4,
        'id': 8
    })
    
    # Create channel-specific scoreboards
    scoreboards = {}
    for channel in range(16):
        scoreboards[channel] = GAXIScoreboard(
            f"Channel_{channel}",
            field_config,
            log=logger
        )
    
    # Transaction router
    class GAXIChannelRouter:
        def __init__(self, scoreboards):
            self.scoreboards = scoreboards
        
        def route_expected(self, packet):
            channel = packet.fields.get('channel', 0)
            if channel in self.scoreboards:
                self.scoreboards[channel].add_expected(packet)
            else:
                print(f"Unknown channel: {channel}")
        
        def route_actual(self, packet):
            channel = packet.fields.get('channel', 0)
            if channel in self.scoreboards:
                self.scoreboards[channel].add_actual(packet)
    
    router = GAXIChannelRouter(scoreboards)
    
    # Generate test traffic
    for channel in range(4):  # Test first 4 channels
        for addr in range(0x1000, 0x2000, 0x100):
            # Write transaction
            write_packet = GAXIPacket(field_config)
            write_packet.fields['addr'] = addr
            write_packet.fields['data'] = 0xDEADBEEF + addr
            write_packet.fields['cmd'] = 1
            write_packet.fields['strb'] = 0xFF
            write_packet.fields['channel'] = channel
            write_packet.fields['id'] = (channel << 4) | (addr & 0xF)
            
            router.route_expected(write_packet)
            
            # Corresponding read transaction
            read_packet = GAXIPacket(field_config)
            read_packet.fields['addr'] = addr
            read_packet.fields['data'] = 0xDEADBEEF + addr
            read_packet.fields['cmd'] = 0
            read_packet.fields['channel'] = channel
            read_packet.fields['id'] = (channel << 4) | (addr & 0xF)
            
            router.route_expected(read_packet)
    
    # ... simulate DUT and route actual transactions ...
    
    # Generate comprehensive report
    total_errors = 0
    for channel, scoreboard in scoreboards.items():
        if scoreboard.transaction_count > 0:
            errors = scoreboard.report()
            total_errors += errors
            pass_rate = scoreboard.result()
            print(f"Channel {channel}: {'PASS' if errors == 0 else 'FAIL'} ({pass_rate:.2%})")
    
    print(f"Overall Result: {'PASS' if total_errors == 0 else 'FAIL'}")
```

### Performance and Coverage Analysis

```python
# Enhanced GAXI scoreboard with analytics
class AnalyticsGAXIScoreboard(GAXIScoreboard):
    def __init__(self, name, field_config, log=None):
        super().__init__(name, field_config, log)
        self.field_coverage = {}
        self.transaction_timing = []
        self.error_patterns = {}
    
    def _compare_transactions(self, expected, actual):
        # Record transaction timing
        if hasattr(actual, 'timestamp'):
            self.transaction_timing.append(actual.timestamp)
        
        # Track field coverage
        for field_name in self.field_config.field_names():
            if field_name not in self.field_coverage:
                self.field_coverage[field_name] = set()
            
            if field_name in actual.fields:
                self.field_coverage[field_name].add(actual.fields[field_name])
        
        # Perform comparison
        result = super()._compare_transactions(expected, actual)
        
        # Track error patterns
        if not result:
            error_key = self._classify_error(expected, actual)
            self.error_patterns[error_key] = self.error_patterns.get(error_key, 0) + 1
        
        return result
    
    def _classify_error(self, expected, actual):
        """Classify error type for pattern analysis"""
        mismatched_fields = []
        for field_name in self.field_config.field_names():
            if (field_name in expected.fields and field_name in actual.fields and
                expected.fields[field_name] != actual.fields[field_name]):
                mismatched_fields.append(field_name)
        
        return tuple(sorted(mismatched_fields))
    
    def get_analytics_report(self):
        # Field coverage analysis
        coverage_report = {}
        for field_name, values in self.field_coverage.items():
            field_width = self.field_config[field_name]
            max_values = 2 ** field_width
            coverage_pct = len(values) / max_values * 100
            coverage_report[field_name] = {
                'unique_values': len(values),
                'max_possible': max_values,
                'coverage_percent': coverage_pct
            }
        
        # Timing analysis
        timing_stats = {}
        if self.transaction_timing:
            timing_stats = {
                'count': len(self.transaction_timing),
                'avg_interval': (max(self.transaction_timing) - min(self.transaction_timing)) / len(self.transaction_timing),
                'throughput': len(self.transaction_timing) / (max(self.transaction_timing) - min(self.transaction_timing))
            }
        
        return {
            'field_coverage': coverage_report,
            'timing_statistics': timing_stats,
            'error_patterns': self.error_patterns,
            'transaction_count': self.transaction_count,
            'error_count': self.error_count
        }

# Usage
analytics_scoreboard = AnalyticsGAXIScoreboard("Analytics", gaxi_field_config, log=logger)

# ... run test ...

report = analytics_scoreboard.get_analytics_report()
print("Coverage Analysis:")
for field, stats in report['field_coverage'].items():
    print(f"  {field}: {stats['coverage_percent']:.1f}% ({stats['unique_values']}/{stats['max_possible']})")

print("Error Pattern Analysis:")
for pattern, count in report['error_patterns'].items():
    print(f"  Fields {pattern}: {count} occurrences")
```

## Best Practices

### Modern Architecture Usage
- Use FieldConfig objects for consistent field definitions
- Leverage modern Packet class with fields dictionary
- Take advantage of automatic timing field exclusion

### Protocol Transformation
- Use TransformScoreboard for cross-protocol verification
- Implement custom transformers for domain-specific conversions
- Validate transformation correctness with known test patterns

### Memory Integration
- Configure appropriate field mappings for memory operations
- Use memory adapters for data consistency verification
- Clear memory state between test phases when appropriate

### Performance Optimization
- Use efficient field comparison methods
- Monitor memory usage in high-throughput scenarios
- Consider batch operations for large test sets

## Integration Points

### Factory Integration
```python
from CocoTBFramework.components.gaxi.gaxi_factories import create_gaxi_scoreboard

# Simplified scoreboard creation
scoreboard = create_gaxi_scoreboard("TestScoreboard", field_config, log=logger)
```

### Monitor Integration
```python
# Connect GAXI monitor to scoreboard
def on_gaxi_packet(packet):
    scoreboard.add_actual(packet)

gaxi_monitor.add_callback(on_gaxi_packet)
```

### Test Environment Integration
```python
# Complete GAXI test environment
class GAXITestEnvironment:
    def __init__(self, dut, clock, field_config):
        self.scoreboard = GAXIScoreboard("TestEnv", field_config, log=logger)
        self.memory_adapter = GAXItoMemoryAdapter(MemoryModel(1024*1024))
        
        # Connect monitors
        self.master_monitor = GAXIMonitor(dut.master, clock, field_config, is_slave=False)
        self.slave_monitor = GAXIMonitor(dut.slave, clock, field_config, is_slave=True)
        
        self.master_monitor.add_callback(self.scoreboard.add_actual)
    
    def verify_transaction(self, expected_packet):
        self.scoreboard.add_expected(expected_packet)
    
    def get_results(self):
        return {
            'errors': self.scoreboard.report(),
            'pass_rate': self.scoreboard.result()
        }
```

The GAXI scoreboard provides comprehensive verification capabilities with modern architecture support, flexible transformation capabilities, and extensive integration options for complex GAXI-based verification environments.