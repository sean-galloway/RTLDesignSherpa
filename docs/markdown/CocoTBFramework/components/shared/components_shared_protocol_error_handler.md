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

# protocol_error_handler.py

Generic error handler that can be used with various protocol implementations to inject errors at specific addresses or address ranges. This module provides fine-grained control over error injection for testing error handling capabilities.

## Overview

The `protocol_error_handler.py` module provides the `ErrorHandler` class, which manages error responses for specific addresses, ID values, or address ranges. This allows comprehensive testing of error handling in verification environments by simulating various error conditions that may occur in real systems.

## Core Class

### ErrorHandler

Error response handler for protocol transactions that manages error regions and individual error transactions.

#### Constructor

```python
ErrorHandler()
```

Creates a new ErrorHandler instance with empty error regions and transactions.

```python
# Create error handler
error_handler = ErrorHandler()
```

#### Core Data Structures

- **`error_regions`**: List of address ranges that should return errors
- **`error_transactions`**: Dictionary mapping (address, ID) pairs to response codes
- **`stats`**: Dictionary tracking error registration and trigger statistics

#### Response Codes

Standard response codes used across protocols:
- **0**: OKAY - Normal successful completion
- **1**: EXOKAY - Exclusive access success (protocol-specific)
- **2**: SLVERR - Slave error (default)
- **3**: DECERR - Decode error

## Error Region Management

### `register_error_region(start_address, end_address, response_code=2)`

Register a memory region that should return errors.

**Parameters:**
- `start_address`: Start address of the region (inclusive)
- `end_address`: End address of the region (inclusive)
- `response_code`: Error response code (default: 2/SLVERR)

```python
# Register error regions
error_handler.register_error_region(0x8000, 0x8FFF, response_code=2)  # SLVERR
error_handler.register_error_region(0x9000, 0x9FFF, response_code=3)  # DECERR

# Register single address as region
error_handler.register_error_region(0xDEAD, 0xDEAD, response_code=2)
```

### `clear_error_regions()`

Clear all registered error regions.

```python
# Clear all error regions
error_handler.clear_error_regions()
```

## Individual Transaction Errors

### `register_error_transaction(address, id_value=None, response_code=2)`

Register a specific address/ID combination for error response.

**Parameters:**
- `address`: Target address
- `id_value`: Transaction ID (None for any ID)
- `response_code`: Error response code (default: 2/SLVERR)

```python
# Error for specific address regardless of ID
error_handler.register_error_transaction(0x1000, response_code=2)

# Error for specific address and ID combination
error_handler.register_error_transaction(0x2000, id_value=5, response_code=3)

# Multiple specific transactions
addresses = [0x3000, 0x3004, 0x3008, 0x300C]
for addr in addresses:
    error_handler.register_error_transaction(addr, response_code=2)
```

### `clear_error_transactions()`

Clear all registered error transactions.

```python
# Clear all individual error transactions
error_handler.clear_error_transactions()
```

### `clear_all_errors()`

Clear all registered errors (both regions and transactions).

```python
# Clear everything
error_handler.clear_all_errors()
```

## Error Checking

### `check_for_error(address, id_value=None)`

Check if a transaction should return an error.

**Parameters:**
- `address`: Target address
- `id_value`: Transaction ID (optional)

**Returns:** Tuple of (should_error, response_code)

```python
# Check for error
should_error, response_code = error_handler.check_for_error(0x8500)
if should_error:
    print(f"Address 0x8500 should return error code {response_code}")

# Check with ID
should_error, response_code = error_handler.check_for_error(0x2000, id_value=5)
if should_error:
    print(f"Transaction to 0x2000 with ID 5 should return error {response_code}")
```

## Statistics

### `get_stats()`

Get statistics about error regions and transactions.

**Returns:** Dictionary with statistics

```python
stats = error_handler.get_stats()
print(f"Error regions registered: {stats['error_regions_registered']}")
print(f"Error transactions registered: {stats['error_transactions_registered']}")
print(f"Errors triggered: {stats['errors_triggered']}")
```

## Usage Patterns

### Basic Error Injection

```python
class ErrorInjectingSlave:
    def __init__(self, dut):
        self.dut = dut
        self.error_handler = ErrorHandler()
        self.memory = {}
        
        # Set up error regions for testing
        self.setup_error_regions()
    
    def setup_error_regions(self):
        """Configure error regions for comprehensive testing"""
        # Decode error region (unmapped addresses)
        self.error_handler.register_error_region(0xF000, 0xFFFF, response_code=3)
        
        # Slave error region (mapped but faulty)
        self.error_handler.register_error_region(0xE000, 0xEFFF, response_code=2)
        
        # Specific problematic addresses
        problematic_addresses = [0x1000, 0x2000, 0x3000]
        for addr in problematic_addresses:
            self.error_handler.register_error_transaction(addr, response_code=2)
    
    @cocotb.coroutine
    def handle_transaction(self, packet):
        """Handle transaction with error injection"""
        address = packet.addr
        
        # Check for configured errors
        should_error, error_code = self.error_handler.check_for_error(address)
        
        if should_error:
            # Return error response
            self.log.info(f"Injecting error {error_code} for address 0x{address:X}")
            packet.resp = error_code
            yield self.send_error_response(packet)
        else:
            # Normal processing
            yield self.process_normal_transaction(packet)
    
    @cocotb.coroutine
    def process_normal_transaction(self, packet):
        """Process normal transaction"""
        if packet.cmd == 1:  # READ
            packet.data = self.memory.get(packet.addr, 0)
            packet.resp = 0  # OKAY
        elif packet.cmd == 2:  # WRITE
            self.memory[packet.addr] = packet.data
            packet.resp = 0  # OKAY
        
        yield self.send_response(packet)
    
    @cocotb.coroutine
    def send_error_response(self, packet):
        """Send error response"""
        # Set error response
        self.dut.resp.value = packet.resp
        self.dut.resp_valid.value = 1
        
        yield RisingEdge(self.dut.clk)
        self.dut.resp_valid.value = 0
```

### Dynamic Error Configuration

```python
class DynamicErrorManager:
    def __init__(self):
        self.error_handler = ErrorHandler()
        self.test_phase = "normal"
        
    def configure_for_test_phase(self, phase):
        """Configure errors based on test phase"""
        self.test_phase = phase
        self.error_handler.clear_all_errors()
        
        if phase == "decode_error_test":
            self._setup_decode_errors()
        elif phase == "slave_error_test":
            self._setup_slave_errors()
        elif phase == "random_error_test":
            self._setup_random_errors()
        elif phase == "stress_test":
            self._setup_stress_errors()
    
    def _setup_decode_errors(self):
        """Set up decode error testing"""
        # Test various unmapped regions
        decode_regions = [
            (0xF000, 0xF0FF),  # Small unmapped region
            (0xFF00, 0xFFFF),  # End of address space
            (0x0, 0xFF),       # Beginning of address space
        ]
        
        for start, end in decode_regions:
            self.error_handler.register_error_region(start, end, response_code=3)
    
    def _setup_slave_errors(self):
        """Set up slave error testing"""
        # Test specific addresses that should cause slave errors
        slave_error_addresses = [
            0x1000, 0x1004, 0x1008, 0x100C,  # Faulty memory bank
            0x2000, 0x2004,                   # Faulty registers
            0x3000,                           # Single faulty location
        ]
        
        for addr in slave_error_addresses:
            self.error_handler.register_error_transaction(addr, response_code=2)
    
    def _setup_random_errors(self):
        """Set up random error injection"""
        import random
        
        # Random error addresses
        for _ in range(20):
            addr = random.randint(0x4000, 0x7FFF)
            error_type = random.choice([2, 3])  # SLVERR or DECERR
            self.error_handler.register_error_transaction(addr, response_code=error_type)
    
    def _setup_stress_errors(self):
        """Set up stress testing with many errors"""
        # Large error region
        self.error_handler.register_error_region(0x8000, 0xBFFF, response_code=2)
        
        # Scattered individual errors
        for addr in range(0x1000, 0x2000, 16):
            self.error_handler.register_error_transaction(addr, response_code=3)
    
    def get_current_configuration(self):
        """Get current error configuration summary"""
        stats = self.error_handler.get_stats()
        return {
            'test_phase': self.test_phase,
            'error_regions': stats['error_regions_registered'],
            'error_transactions': stats['error_transactions_registered'],
            'total_errors_configured': stats['error_regions_registered'] + stats['error_transactions_registered']
        }
```

### AXI Error Handler Example

```python
class AXIErrorHandler:
    def __init__(self):
        self.error_handler = ErrorHandler()
        self.outstanding_errors = {}  # Track multi-beat transaction errors
    
    def setup_axi_error_scenarios(self):
        """Set up AXI-specific error scenarios"""
        # Address decode errors
        self.error_handler.register_error_region(0x80000000, 0x8FFFFFFF, response_code=3)  # DECERR
        
        # Slave errors for protected regions
        self.error_handler.register_error_region(0x70000000, 0x7FFFFFFF, response_code=2)  # SLVERR
        
        # ID-specific errors for testing multiple outstanding transactions
        for transaction_id in [5, 10, 15]:
            self.error_handler.register_error_transaction(
                0x60000000, id_value=transaction_id, response_code=2
            )
    
    def check_write_address_error(self, awaddr, awid):
        """Check for write address errors"""
        should_error, error_code = self.error_handler.check_for_error(awaddr, awid)
        
        if should_error:
            # Store error for write response
            self.outstanding_errors[awid] = error_code
            self.log.info(f"Write address error: AWID={awid}, AWADDR=0x{awaddr:X}, Error={error_code}")
        
        return should_error, error_code
    
    def check_read_address_error(self, araddr, arid):
        """Check for read address errors"""
        should_error, error_code = self.error_handler.check_for_error(araddr, arid)
        
        if should_error:
            # Store error for read data response
            self.outstanding_errors[arid] = error_code
            self.log.info(f"Read address error: ARID={arid}, ARADDR=0x{araddr:X}, Error={error_code}")
        
        return should_error, error_code
    
    def get_write_response_error(self, bid):
        """Get write response error code"""
        if bid in self.outstanding_errors:
            error_code = self.outstanding_errors.pop(bid)
            return True, error_code
        return False, 0
    
    def get_read_data_error(self, rid):
        """Get read data error code"""
        if rid in self.outstanding_errors:
            error_code = self.outstanding_errors[rid]
            # Don't remove yet - might be multi-beat
            return True, error_code
        return False, 0
    
    def clear_transaction_error(self, transaction_id):
        """Clear error for completed transaction"""
        if transaction_id in self.outstanding_errors:
            del self.outstanding_errors[transaction_id]
```

### Test Framework Integration

```python
@cocotb.test()
def error_injection_test(dut):
    """Comprehensive error injection testing"""
    
    # Set up error handler
    error_handler = ErrorHandler()
    
    # Configure error scenarios
    test_scenarios = [
        {
            'name': 'decode_errors',
            'regions': [(0xF000, 0xFFFF, 3)],
            'transactions': []
        },
        {
            'name': 'slave_errors',
            'regions': [(0xE000, 0xEFFF, 2)],
            'transactions': [(0x1000, None, 2), (0x2000, None, 2)]
        },
        {
            'name': 'mixed_errors',
            'regions': [(0xD000, 0xDFFF, 3)],
            'transactions': [(0x3000, 5, 2), (0x4000, 10, 3)]
        }
    ]
    
    for scenario in test_scenarios:
        cocotb.log.info(f"Testing scenario: {scenario['name']}")
        
        # Clear previous configuration
        error_handler.clear_all_errors()
        
        # Configure error regions
        for start, end, code in scenario['regions']:
            error_handler.register_error_region(start, end, code)
        
        # Configure error transactions
        for addr, id_val, code in scenario['transactions']:
            error_handler.register_error_transaction(addr, id_val, code)
        
        # Run test with this configuration
        yield run_error_test_sequence(dut, error_handler, scenario['name'])
        
        # Validate error statistics
        stats = error_handler.get_stats()
        assert stats['errors_triggered'] > 0, f"No errors triggered in {scenario['name']}"
        
        cocotb.log.info(f"Scenario {scenario['name']}: {stats['errors_triggered']} errors triggered")

@cocotb.coroutine
def run_error_test_sequence(dut, error_handler, scenario_name):
    """Run test sequence with error checking"""
    
    # Test addresses that should cause errors
    test_addresses = [0xF000, 0xE500, 0x1000, 0x2000, 0x3000, 0x4000]
    test_ids = [0, 5, 10, 15]
    
    for addr in test_addresses:
        for test_id in test_ids:
            # Check if this should cause an error
            should_error, error_code = error_handler.check_for_error(addr, test_id)
            
            # Drive transaction
            yield drive_transaction(dut, addr, test_id)
            
            # Check response
            response = yield capture_response(dut)
            
            if should_error:
                assert response.error_code == error_code, \
                    f"Expected error {error_code}, got {response.error_code} for addr=0x{addr:X}, id={test_id}"
                cocotb.log.info(f"Correctly received error {error_code} for 0x{addr:X}")
            else:
                assert response.error_code == 0, \
                    f"Unexpected error {response.error_code} for addr=0x{addr:X}, id={test_id}"

@cocotb.coroutine
def drive_transaction(dut, addr, transaction_id):
    """Drive transaction to DUT"""
    dut.addr.value = addr
    dut.id.value = transaction_id
    dut.valid.value = 1
    
    yield RisingEdge(dut.clk)
    dut.valid.value = 0

@cocotb.coroutine
def capture_response(dut):
    """Capture response from DUT"""
    yield RisingEdge(dut.response_valid)
    
    response = type('Response', (), {})()
    response.error_code = int(dut.response_code.value)
    response.id = int(dut.response_id.value)
    
    return response
```

### Advanced Error Patterns

```python
class AdvancedErrorPatterns:
    def __init__(self):
        self.error_handler = ErrorHandler()
        self.error_patterns = {}
    
    def create_intermittent_errors(self, address, error_rate=0.1):
        """Create intermittent errors at specific address"""
        import random
        
        def intermittent_check(addr, id_val=None):
            if addr == address and random.random() < error_rate:
                return True, 2  # SLVERR
            return False, 0
        
        # Store custom pattern
        self.error_patterns[f'intermittent_{address:X}'] = intermittent_check
    
    def create_burst_errors(self, base_address, burst_length):
        """Create errors for burst transactions"""
        # Register errors for entire burst range
        end_address = base_address + (burst_length * 4) - 1
        self.error_handler.register_error_region(base_address, end_address, response_code=2)
    
    def create_id_based_errors(self, problematic_ids):
        """Create errors based on transaction IDs"""
        for transaction_id in problematic_ids:
            # Error for any address with this ID
            for addr in range(0x1000, 0x2000, 4):
                self.error_handler.register_error_transaction(addr, transaction_id, response_code=2)
    
    def create_temporal_errors(self, start_time, end_time, addresses):
        """Create time-based error injection"""
        # This would require integration with simulation time
        # Store temporal error configuration
        self.temporal_errors = {
            'start_time': start_time,
            'end_time': end_time,
            'addresses': addresses
        }
    
    def check_advanced_error(self, address, id_value=None, current_time=None):
        """Check for advanced error patterns"""
        # Check standard error handler first
        should_error, error_code = self.error_handler.check_for_error(address, id_value)
        
        if should_error:
            return should_error, error_code
        
        # Check custom patterns
        for pattern_name, pattern_func in self.error_patterns.items():
            should_error, error_code = pattern_func(address, id_value)
            if should_error:
                return should_error, error_code
        
        # Check temporal errors
        if hasattr(self, 'temporal_errors') and current_time:
            temporal = self.temporal_errors
            if (temporal['start_time'] <= current_time <= temporal['end_time'] and
                address in temporal['addresses']):
                return True, 2
        
        return False, 0
```

### Error Analysis and Reporting

```python
class ErrorAnalyzer:
    def __init__(self, error_handler):
        self.error_handler = error_handler
        self.error_log = []
    
    def log_error_event(self, address, id_value, error_code, timestamp):
        """Log error event for analysis"""
        self.error_log.append({
            'address': address,
            'id': id_value,
            'error_code': error_code,
            'timestamp': timestamp,
            'error_type': self._get_error_type_name(error_code)
        })
    
    def _get_error_type_name(self, error_code):
        """Convert error code to readable name"""
        error_names = {0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}
        return error_names.get(error_code, f'UNKNOWN_{error_code}')
    
    def generate_error_report(self):
        """Generate comprehensive error analysis report"""
        stats = self.error_handler.get_stats()
        
        # Analyze error distribution
        error_types = {}
        address_patterns = {}
        
        for event in self.error_log:
            # Count error types
            error_type = event['error_type']
            error_types[error_type] = error_types.get(error_type, 0) + 1
            
            # Count address patterns
            addr_range = (event['address'] // 0x1000) * 0x1000  # Group by 4KB
            address_patterns[addr_range] = address_patterns.get(addr_range, 0) + 1
        
        report = {
            'configuration_stats': stats,
            'runtime_stats': {
                'total_errors_logged': len(self.error_log),
                'error_type_distribution': error_types,
                'address_pattern_distribution': address_patterns
            },
            'coverage_analysis': self._analyze_error_coverage()
        }
        
        return report
    
    def _analyze_error_coverage(self):
        """Analyze how well error scenarios were exercised"""
        # Check if configured errors were actually triggered
        # This would require tracking which specific configurations caused errors
        return {
            'configured_regions_hit': "Analysis would go here",
            'configured_transactions_hit': "Analysis would go here",
            'coverage_percentage': 85.5  # Example
        }
```

## Best Practices

### 1. **Organize Errors by Test Phase**
```python
def setup_test_phase_errors(error_handler, phase):
    error_handler.clear_all_errors()
    
    if phase == "basic_functionality":
        # Minimal errors for basic testing
        pass
    elif phase == "error_handling":
        # Comprehensive error scenarios
        setup_comprehensive_errors(error_handler)
    elif phase == "stress_testing":
        # Heavy error injection
        setup_stress_errors(error_handler)
```

### 2. **Use Appropriate Error Types**
```python
# Decode errors for unmapped addresses
error_handler.register_error_region(0xF000, 0xFFFF, response_code=3)  # DECERR

# Slave errors for mapped but faulty regions
error_handler.register_error_region(0xE000, 0xEFFF, response_code=2)  # SLVERR
```

### 3. **Test Both Region and Transaction Errors**
```python
# Test broad regions
error_handler.register_error_region(0x8000, 0x8FFF, response_code=2)

# Test specific transactions
error_handler.register_error_transaction(0x1000, response_code=3)
```

### 4. **Monitor Error Statistics**
```python
# Regular statistics monitoring
def check_error_coverage():
    stats = error_handler.get_stats()
    if stats['errors_triggered'] == 0:
        log.warning("No errors have been triggered yet")
```

### 5. **Clear Errors Between Test Phases**
```python
# Always clear errors when changing test scenarios
error_handler.clear_all_errors()
setup_new_test_errors()
```

The ErrorHandler provides a comprehensive framework for testing error handling capabilities across different protocols, enabling thorough validation of error response mechanisms in verification environments.
