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

# apb_scoreboard.py

APB (Advanced Peripheral Bus) scoreboard implementation for verifying APB transactions. This module provides both single-slave and multi-slave APB verification capabilities with comprehensive transaction matching and protocol transformation support.

## Overview

The APB scoreboard system provides:
- **Single-Slave Verification**: Basic APB transaction verification for single-slave systems
- **Multi-Slave Support**: Automatic transaction routing for multi-slave APB systems
- **Direction-Aware Comparison**: Separate handling of read and write transactions
- **Enhanced Error Reporting**: Field-by-field mismatch analysis
- **Protocol Transformation**: APB to GAXI conversion support

## Classes

### APBScoreboard

Core APB transaction verification for single-slave systems.

```python
class APBScoreboard(BaseScoreboard):
    def __init__(self, name, addr_width=32, data_width=32, log=None)
```

**Parameters:**
- `name`: Scoreboard name for identification
- `addr_width`: Address bus width in bits (default: 32)
- `data_width`: Data bus width in bits (default: 32)
- `log`: Logger instance for detailed reporting

**Key Attributes:**
- `addr_width`: Address bus width
- `data_width`: Data bus width  
- `strb_width`: Strobe width (data_width // 8)
- `master_transactions`: Dictionary tracking transactions by master ID

## Core Methods

### Transaction Comparison

#### `_compare_transactions(expected, actual)`
Compare APB packets based on protocol fields.

**Parameters:**
- `expected`: Expected APB transaction (APBPacket)
- `actual`: Actual APB transaction (APBPacket)

**Returns:**
- `bool`: True if transactions match, False otherwise

**Comparison Logic:**
- Validates transaction types (must be APBPacket instances)
- Uses APBPacket's built-in `__eq__` method
- Compares direction, address, data, and control fields

```python
# Automatic comparison when both transactions available
scoreboard.add_expected(expected_apb_packet)
scoreboard.add_actual(actual_apb_packet)  # Triggers comparison
```

#### `_log_mismatch(expected, actual)`
Enhanced mismatch logging with field-by-field analysis.

**Parameters:**
- `expected`: Expected APB transaction
- `actual`: Actual APB transaction

**Detailed Logging:**
- Direction mismatch detection
- Address field comparison
- Data field analysis for both read and write
- Strobe field validation
- Enable signal checking

```python
# Example mismatch log output:
# APB Cycle mismatch:
#   Expected: WRITE addr=0x1000 data=0xDEADBEEF strb=0xF
#   Actual:   WRITE addr=0x1000 data=0xBEEFDEAD strb=0xF
#   Data mismatch: expected=0xDEADBEEF, actual=0xBEEFDEAD
```

## Multi-Slave Support

### APBMultiSlaveScoreboard

Advanced scoreboard for multi-slave APB systems with automatic transaction routing.

```python
class APBMultiSlaveScoreboard:
    def __init__(self, name, num_slaves, addr_width=32, data_width=32, log=None)
```

**Parameters:**
- `name`: Scoreboard name
- `num_slaves`: Number of slave devices
- `addr_width`: Address bus width (default: 32)
- `data_width`: Data bus width (default: 32)  
- `log`: Logger instance

**Architecture:**
- Creates individual `APBScoreboard` for each slave
- Automatic address-based transaction routing
- Configurable address mapping per slave
- Combined reporting across all slaves

### Address Mapping

#### `set_address_map(addr_map)`
Configure custom address ranges for slave selection.

**Parameters:**
- `addr_map`: List of `(base_addr, end_addr)` tuples for each slave

**Default Mapping:**
- Slave 0: 0x0000 - 0x0FFC
- Slave 1: 0x1000 - 0x1FFC
- Slave N: N*0x1000 - (N*0x1000 + 0xFFC)

```python
# Custom address mapping
scoreboard = APBMultiSlaveScoreboard("MultiSlave", num_slaves=3)
addr_map = [
    (0x0000, 0x7FFF),  # Slave 0: 32KB
    (0x8000, 0xBFFF),  # Slave 1: 16KB  
    (0xC000, 0xFFFF),  # Slave 2: 16KB
]
scoreboard.set_address_map(addr_map)
```

#### `get_slave_idx(addr)`
Determine target slave for given address.

**Parameters:**
- `addr`: Address to route

**Returns:**
- `int`: Slave index, or modulo-based routing if no mapping match

**Routing Logic:**
1. Check configured address map for exact range match
2. Fall back to modulo routing: `addr // 0x1000 % num_slaves`

### Transaction Management

#### `add_master_transaction(transaction, master_id)`
Add transaction from master with automatic slave routing.

**Parameters:**
- `transaction`: APB transaction to route
- `master_id`: Master identifier for tracking

**Behavior:**
- Determines target slave using `get_slave_idx()`
- Routes transaction to appropriate slave scoreboard
- Maintains master transaction tracking

```python
# Automatic routing based on address
scoreboard.add_master_transaction(transaction, master_id=0)
# Transaction routed to correct slave based on address
```

#### `add_slave_transaction(transaction, slave_idx)`
Add transaction from specific slave.

**Parameters:**
- `transaction`: APB transaction from slave
- `slave_idx`: Slave index (0 to num_slaves-1)

**Error Handling:**
- Validates slave index range
- Logs errors for invalid slave indices

### Reporting

#### `report()`
Generate comprehensive multi-slave report.

**Returns:**
- `str`: Combined report from all slave scoreboards

**Report Format:**
```
APB Multi-Slave Scoreboard Report (MultiSlave):
Slave 0: PASS
Slave 1: FAIL (0.95)
Slave 2: PASS
Overall: FAIL
```

## Protocol Transformation

### APBtoGAXITransformer

Transformer for converting APB transactions to GAXI packets.

```python
class APBtoGAXITransformer(ProtocolTransformer):
    def __init__(self, gaxi_field_config, packet_class, log=None)
```

**Parameters:**
- `gaxi_field_config`: GAXI field configuration
- `packet_class`: GAXI packet class for creating instances
- `log`: Logger instance

### Transformation Logic

#### `transform(apb_cycle)`
Convert APB transaction to GAXI packet(s).

**Parameters:**
- `apb_cycle`: APB packet to transform

**Returns:**
- `List[GAXIPacket]`: List of transformed GAXI packets

**Field Mapping:**
- `apb.paddr` → `gaxi.addr`
- `apb.pwdata/prdata` → `gaxi.data` (direction-dependent)
- `apb.pstrb` → `gaxi.strb` (write transactions only)

```python
# Create transformer
transformer = APBtoGAXITransformer(gaxi_field_config, GAXIPacket, log=logger)

# Use with scoreboard
gaxi_scoreboard = GAXIScoreboard("Bridge", gaxi_field_config, log=logger)
gaxi_scoreboard.set_transformer(transformer)

# APB transactions automatically converted for GAXI comparison
gaxi_scoreboard.add_expected(apb_transaction)  # Transformed to GAXI
gaxi_scoreboard.add_actual(gaxi_packet)        # Direct comparison
```

## Usage Examples

### Basic Single-Slave Verification

```python
from CocoTBFramework.scoreboards.apb_scoreboard import APBScoreboard
from CocoTBFramework.components.apb.apb_packet import APBPacket

# Create scoreboard
scoreboard = APBScoreboard("APB_Slave", addr_width=32, data_width=32, log=logger)

# Create test transactions
expected = APBPacket()
expected.direction = 'WRITE'
expected.paddr = 0x1000
expected.pwdata = 0xDEADBEEF
expected.pstrb = 0xF

actual = APBPacket()
actual.direction = 'WRITE'  
actual.paddr = 0x1000
actual.pwdata = 0xDEADBEEF
actual.pstrb = 0xF

# Verify transactions
scoreboard.add_expected(expected)
scoreboard.add_actual(actual)

# Check results
error_count = scoreboard.report()
pass_rate = scoreboard.result()
print(f"Verification: {'PASS' if error_count == 0 else 'FAIL'} ({pass_rate:.2%})")
```

### Multi-Slave System Verification

```python
from CocoTBFramework.scoreboards.apb_scoreboard import APBMultiSlaveScoreboard

# Create multi-slave scoreboard
scoreboard = APBMultiSlaveScoreboard("APB_System", num_slaves=4, log=logger)

# Configure custom address mapping
addr_map = [
    (0x0000, 0x0FFF),  # Peripheral 0: GPIO
    (0x1000, 0x1FFF),  # Peripheral 1: UART
    (0x2000, 0x2FFF),  # Peripheral 2: SPI
    (0x3000, 0x3FFF),  # Peripheral 3: I2C
]
scoreboard.set_address_map(addr_map)

# Add transactions - automatically routed
gpio_transaction = create_apb_transaction(addr=0x0100, data=0xFF)  # → Slave 0
uart_transaction = create_apb_transaction(addr=0x1004, data=0x55)  # → Slave 1

scoreboard.add_master_transaction(gpio_transaction, master_id=0)
scoreboard.add_master_transaction(uart_transaction, master_id=0)

# Add expected slave responses
scoreboard.add_slave_transaction(gpio_response, slave_idx=0)
scoreboard.add_slave_transaction(uart_response, slave_idx=1)

# Generate comprehensive report
print(scoreboard.report())
```

### Cross-Protocol Bridge Verification

```python
from CocoTBFramework.scoreboards.apb_scoreboard import APBtoGAXITransformer
from CocoTBFramework.scoreboards.gaxi_scoreboard import GAXIScoreboard

# Create transformer and target scoreboard
transformer = APBtoGAXITransformer(gaxi_field_config, GAXIPacket, log=logger)
bridge_scoreboard = GAXIScoreboard("APB_GAXI_Bridge", gaxi_field_config, log=logger)
bridge_scoreboard.set_transformer(transformer)

# Verify APB input produces correct GAXI output
apb_input = create_apb_write(addr=0x2000, data=0x12345678)
gaxi_output = monitor_gaxi_transaction()

bridge_scoreboard.add_expected(apb_input)    # Automatically transformed
bridge_scoreboard.add_actual(gaxi_output)   # Direct GAXI comparison

# Analysis
errors = bridge_scoreboard.report()
if errors == 0:
    print("Bridge verification passed")
else:
    print(f"Bridge verification failed: {errors} errors")
```

### Enhanced Error Analysis

```python
# Custom scoreboard with detailed error reporting
class DetailedAPBScoreboard(APBScoreboard):
    def _log_mismatch(self, expected, actual):
        super()._log_mismatch(expected, actual)
        
        # Additional analysis
        if self.log:
            if expected.paddr != actual.paddr:
                addr_diff = actual.paddr - expected.paddr
                self.log.error(f"  Address offset: 0x{addr_diff:X}")
            
            if hasattr(expected, 'pwdata') and hasattr(actual, 'pwdata'):
                if expected.pwdata != actual.pwdata:
                    xor_result = expected.pwdata ^ actual.pwdata
                    self.log.error(f"  Data XOR: 0x{xor_result:08X}")

# Usage with enhanced reporting
detailed_scoreboard = DetailedAPBScoreboard("Detailed", log=logger)
```

## Best Practices

### Address Mapping Configuration
- Define clear, non-overlapping address ranges for multi-slave systems
- Use power-of-2 boundaries for efficient decoding
- Document address map in test configuration

### Transaction Tracking
- Use meaningful master IDs for transaction correlation
- Clear scoreboards between test phases
- Monitor queue sizes in long-running tests

### Error Analysis
- Enable detailed logging for debugging mismatches
- Use field-by-field comparison for systematic analysis
- Preserve mismatch pairs for post-test analysis

### Performance Optimization
- Configure appropriate queue sizes for expected transaction volumes
- Use batch operations for large transaction sets
- Clear completed transactions periodically

## Integration Points

### Monitor Integration
```python
# Connect APB monitor to scoreboard
def on_apb_transaction(packet):
    scoreboard.add_actual(packet)

apb_monitor.add_callback(on_apb_transaction)
```

### Test Sequence Integration
```python
# Generate expected transactions from test sequence
sequence = APBSequence("test_pattern")
for packet in sequence.generate():
    scoreboard.add_expected(packet)
```

The APB scoreboard provides comprehensive verification capabilities for both simple single-slave and complex multi-slave APB systems, with robust error reporting and cross-protocol transformation support.