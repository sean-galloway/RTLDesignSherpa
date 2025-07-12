# cdc_handshake.py

CDC Handshake Testbench with sophisticated randomization and comprehensive clock domain crossing verification for AMBA protocols.

## Overview

The `cdc_handshake.py` module provides the `CDCHandshakeTB` class, a comprehensive testbench for verifying clock domain crossing (CDC) implementations. It combines dual clock domain support, advanced timing analysis, sophisticated randomization patterns, and memory model integration to enable thorough CDC verification.

### Key Features
- **Dual clock domain architecture**: Independent source and destination clock domains with configurable frequencies
- **Advanced timing analysis**: CDC latency measurement, timing violation detection, and performance metrics
- **Sophisticated randomization**: 20+ randomization profiles including CDC-specific patterns
- **Memory model integration**: Shared memory across domains for data integrity verification
- **Comprehensive test patterns**: From basic incremental to stress testing with burst patterns
- **FlexConfigGen integration**: Advanced randomization configuration generation

## Class Definition

### CDCHandshakeTB

Main class for CDC handshake verification with dual clock domain support.

#### Constructor

```python
CDCHandshakeTB(dut)
```

**Parameters:**
- `dut`: Device under test (CocoTB DUT object)

**Environment Variables:**
- `TEST_ADDR_WIDTH`: Address width in bits (default: 32)
- `TEST_DATA_WIDTH`: Data width in bits (default: 32)  
- `TEST_LEVEL`: Test complexity level - 'basic', 'medium', 'full' (default: 'basic')
- `clk_src_PERIOD_NS`: Source clock period in nanoseconds (default: 50)
- `clk_dst_PERIOD_NS`: Destination clock period in nanoseconds (default: 10)
- `SUPER_DEBUG`: Enable detailed debugging - 'true'/'false' (default: 'false')

```python
# Basic setup with default clocks
tb = CDCHandshakeTB(dut)

# Setup with custom clock frequencies via environment
os.environ['clk_src_PERIOD_NS'] = '20'  # 50MHz source
os.environ['clk_dst_PERIOD_NS'] = '8'   # 125MHz destination
os.environ['TEST_LEVEL'] = 'medium'
tb = CDCHandshakeTB(dut)
```

## Clock Domain Configuration

### Automatic Clock Analysis

The testbench automatically calculates clock relationships and configures CDC-aware testing:

```python
# Calculated properties
tb.clk_src_FREQ_MHZ = 1000 / tb.clk_src_PERIOD_NS
tb.clk_dst_FREQ_MHZ = 1000 / tb.clk_dst_PERIOD_NS  
tb.clock_ratio = tb.clk_dst_PERIOD_NS / tb.clk_src_PERIOD_NS

# CDC type detection
if tb.clock_ratio > 1:
    cdc_type = "Fast->Slow"
elif tb.clock_ratio < 1:
    cdc_type = "Slow->Fast"
else:
    cdc_type = "Same Freq"
```

### Clock Domain Components

Each clock domain has dedicated GAXI components:

**Source Domain:**
- `src_master`: GAXI master for transaction generation
- `src_monitor`: Monitor for source domain transactions

**Destination Domain:**
- `dst_slave`: GAXI slave for transaction responses
- `dst_monitor`: Monitor for destination domain transactions

## Randomization Configuration

### CDC-Specific Randomization Profiles

The testbench includes 20+ randomization profiles optimized for CDC testing:

#### Standard Profiles
- `'backtoback'`: Zero delay for maximum throughput
- `'fast'`: Minimal delays for high-performance testing
- `'constrained'`: Balanced randomization for general verification
- `'moderate'`: Moderate delays for realistic scenarios
- `'slow'`: Extended delays for timing verification

#### CDC-Specific Profiles
- `'cdc_conservative'`: Safe CDC timing with longer delays
- `'cdc_aggressive'`: Fast CDC timing for stress testing
- `'cdc_mixed_freq'`: Mixed frequency aware patterns
- `'cdc_burst_stress'`: Burst patterns with pauses for CDC stress
- `'cdc_jitter'`: Jittery timing patterns to test CDC robustness
- `'cdc_slow_domain'`: Patterns optimized for slow domain simulation
- `'cdc_fast_domain'`: Patterns optimized for fast domain simulation
- `'cdc_metastable'`: Patterns designed to test metastability handling
- `'cdc_ratio_sync'`: Clock ratio aware synchronous patterns
- `'cdc_ratio_async'`: Clock ratio aware asynchronous patterns

```python
# Get available randomization configurations
config_names = tb.get_randomizer_config_names()
print(f"Available configs: {config_names}")

# Use CDC-specific configuration
await tb.run_simple_incremental_test(50, 'cdc_mixed_freq')
```

## Core Test Methods

### `run_simple_incremental_test(count=20, randomizer_config='moderate', test_name="Simple Incremental")`

Run basic incremental test with specified randomization configuration.

**Parameters:**
- `count`: Number of transactions to send
- `randomizer_config`: Randomization configuration name
- `test_name`: Test identifier for logging

**Returns:** True if test passed, False if errors detected

```python
# Basic incremental test
success = await tb.run_simple_incremental_test(100, 'cdc_conservative')

# High-stress incremental test
success = await tb.run_simple_incremental_test(500, 'cdc_aggressive', "Stress Test")
```

### `run_walking_bits_test(test_name="Walking Bits")`

Test with walking bits patterns to verify data integrity across CDC.

**Parameters:**
- `test_name`: Test identifier for logging

**Returns:** True if test passed, False if errors detected

```python
# Walking bits test for data integrity
success = await tb.run_walking_bits_test("CDC Data Integrity")
```

### `run_stress_test(count=100, randomizer_config='cdc_mixed_freq', test_name="Stress Test")`

Run stress test with mixed patterns including deterministic and random data.

**Parameters:**
- `count`: Number of transactions to send
- `randomizer_config`: Randomization configuration name  
- `test_name`: Test identifier for logging

**Returns:** True if test passed, False if errors detected

```python
# Mixed frequency stress test
success = await tb.run_stress_test(200, 'cdc_mixed_freq')

# Burst stress with CDC-specific patterns
success = await tb.run_stress_test(150, 'cdc_burst_stress', "CDC Burst Stress")
```

### `run_back_to_back_test(count=50, test_name="Back-to-Back")`

Test back-to-back transactions with minimal delays to stress CDC implementation.

**Parameters:**
- `count`: Number of transactions to send
- `test_name`: Test identifier for logging

**Returns:** True if test passed, False if errors detected

```python
# Back-to-back stress test
success = await tb.run_back_to_back_test(100, "CDC Stress")
```

## Comprehensive Test Suites

### `run_basic_tests()`

Execute basic test suite (2-3 minutes duration).

**Tests Included:**
- Simple incremental test (10 transactions)
- Back-to-back test (15 transactions)
- Walking bits test

**Returns:** True if all tests passed

```python
# Run basic test suite
success = await tb.run_basic_tests()
assert success, "Basic test suite failed"
```

### `run_medium_tests()`

Execute medium test suite (5-8 minutes duration).

**Tests Included:**
- Multiple incremental tests with different configurations
- Extended back-to-back testing
- Walking bits verification
- Stress testing with mixed frequencies
- Comprehensive randomizer sweep

**Returns:** True if all tests passed

```python
# Run medium test suite  
success = await tb.run_medium_tests()
assert success, "Medium test suite failed"
```

### `run_full_tests()`

Execute full test suite (15-25 minutes duration).

**Tests Included:**
- Comprehensive incremental testing
- Multiple stress test configurations
- Extended randomizer sweeps
- All CDC-specific test patterns
- Maximum coverage scenarios

**Returns:** True if all tests passed

```python
# Run comprehensive test suite
success = await tb.run_full_tests()
assert success, "Full test suite failed"
```

## Analysis and Monitoring

### CDC Timing Analysis

The testbench automatically performs CDC timing analysis:

```python
def _analyze_cdc_timing(self, dst_transaction):
    """Analyze CDC timing for destination transaction"""
    # Find corresponding source transaction
    src_transaction = self.find_matching_source_transaction(dst_transaction)
    
    if src_transaction:
        # Calculate CDC timing metrics
        cdc_latency = dst_transaction.end_time - src_transaction.end_time
        src_cycles = cdc_latency / self.clk_src_PERIOD_NS
        dst_cycles = cdc_latency / self.clk_dst_PERIOD_NS
        
        timing_data = {
            'cdc_latency_ns': cdc_latency,
            'src_cycles': src_cycles,
            'dst_cycles': dst_cycles,
            'clock_ratio': self.clock_ratio
        }
        
        # Store for analysis
        self.timing_analysis.append(timing_data)
```

### `get_comprehensive_statistics()`

Get detailed statistics about test execution and CDC performance.

**Returns:** Dictionary with comprehensive statistics

```python
stats = tb.get_comprehensive_statistics()

# Example statistics
{
    'transactions_sent': 150,
    'transactions_verified': 150,
    'total_errors': 0,
    'cdc_violations': 0,
    'timing_errors': 0,
    'data_errors': 0,
    'test_duration_ns': 1500000,
    'throughput_tps': 100000,
    'avg_cdc_latency_ns': 45.2,
    'min_cdc_latency_ns': 20.1,
    'max_cdc_latency_ns': 85.7,
    'clock_ratio': 0.2,
    'src_frequency_mhz': 20.0,
    'dst_frequency_mhz': 100.0
}
```

## Transaction Management

### `send_transaction(is_write, addr, data=None, strobe=None, prot=0)`

Send a single transaction across the CDC interface.

**Parameters:**
- `is_write`: True for write, False for read
- `addr`: Address for transaction
- `data`: Data for write transactions (None for reads)
- `strobe`: Byte strobe (auto-generated if None)
- `prot`: Protection attributes (default: 0)

**Returns:** Transaction packet with timing information

```python
# Send write transaction
packet = await tb.send_transaction(
    is_write=True,
    addr=0x1000,
    data=0xDEADBEEF,
    strobe=0xF
)

# Send read transaction
packet = await tb.send_transaction(
    is_write=False,
    addr=0x2000
)
```

### `wait_for_completion(expected_count=None, timeout_cycles=None)`

Wait for transactions to complete with CDC-aware timing.

**Parameters:**
- `expected_count`: Expected number of transactions (optional)
- `timeout_cycles`: Timeout in cycles (default: 10000)

**Returns:** True if completion successful, False if timeout

```python
# Wait for all transactions to complete
success = await tb.wait_for_completion(expected_count=50)

# Wait with custom timeout
success = await tb.wait_for_completion(
    expected_count=100,
    timeout_cycles=5000
)
```

## Usage Patterns

### Basic CDC Verification

```python
import cocotb
from CocoTBFramework.tbclasses.amba.cdc_handshake import CDCHandshakeTB

@cocotb.test()
async def test_cdc_basic(dut):
    # Set up CDC testbench
    tb = CDCHandshakeTB(dut)
    await tb.initialize()
    
    # Run basic CDC test
    success = await tb.run_simple_incremental_test(50, 'cdc_conservative')
    assert success, "CDC basic test failed"
    
    # Get CDC statistics
    stats = tb.get_comprehensive_statistics()
    tb.log.info(f"CDC latency: {stats['avg_cdc_latency_ns']:.2f}ns")
    
    assert stats['total_errors'] == 0, f"Found {stats['total_errors']} errors"
```

### Advanced CDC Testing with Multiple Configurations

```python
@cocotb.test()
async def test_cdc_comprehensive(dut):
    tb = CDCHandshakeTB(dut)
    await tb.initialize()
    
    # Test multiple CDC configurations
    cdc_configs = ['cdc_conservative', 'cdc_aggressive', 'cdc_mixed_freq', 'cdc_burst_stress']
    
    results = {}
    for config in cdc_configs:
        tb.log.info(f"Testing configuration: {config}")
        
        success = await tb.run_stress_test(100, config, f"Stress-{config}")
        stats = tb.get_comprehensive_statistics()
        
        results[config] = {
            'success': success,
            'latency': stats['avg_cdc_latency_ns'],
            'throughput': stats['throughput_tps']
        }
        
        assert success, f"Configuration {config} failed"
    
    # Analyze results
    for config, result in results.items():
        tb.log.info(f"{config}: {result['latency']:.2f}ns latency, "
                   f"{result['throughput']:.0f} TPS")
```

### Test Level Based Execution

```python
@cocotb.test()
async def test_cdc_adaptive(dut):
    tb = CDCHandshakeTB(dut)
    await tb.initialize()
    
    # Run tests based on TEST_LEVEL environment variable
    if tb.TEST_LEVEL == 'basic':
        success = await tb.run_basic_tests()
    elif tb.TEST_LEVEL == 'medium':
        success = await tb.run_medium_tests()
    elif tb.TEST_LEVEL == 'full':
        success = await tb.run_full_tests()
    else:
        # Default to basic
        success = await tb.run_basic_tests()
    
    assert success, f"Test level {tb.TEST_LEVEL} failed"
    
    # Report final statistics
    stats = tb.get_comprehensive_statistics()
    tb.log.info(f"Test completed: {stats['transactions_verified']} transactions verified")
    tb.log.info(f"CDC efficiency: {stats['avg_cdc_latency_ns']:.2f}ns average latency")
```

### Integration with Power Management

```python
from CocoTBFramework.tbclasses.amba.amba_cg_ctrl import AxiClockGateCtrl

@cocotb.test()
async def test_cdc_with_power(dut):
    # Set up CDC testbench
    cdc_tb = CDCHandshakeTB(dut)
    await cdc_tb.initialize()
    
    # Set up power monitoring
    clock_gate = AxiClockGateCtrl(
        dut,
        instance_path="power_ctrl",
        user_valid_signals=["src_valid"],
        axi_valid_signals=["dst_valid"]
    )
    clock_gate.enable_clock_gating(True)
    clock_gate.set_idle_count(8)
    
    # Run CDC test with power monitoring
    cdc_task = cocotb.start_soon(
        cdc_tb.run_stress_test(200, 'cdc_burst_stress')
    )
    power_task = cocotb.start_soon(
        clock_gate.monitor_activity(15000, 'ns')
    )
    
    # Wait for completion
    cdc_success = await cdc_task
    power_stats = await power_task
    
    # Validate both CDC and power performance
    assert cdc_success, "CDC test failed"
    assert power_stats['gated_percent'] > 20, "Insufficient power savings"
    
    cdc_stats = cdc_tb.get_comprehensive_statistics()
    
    cdc_tb.log.info(f"CDC test passed: {cdc_stats['avg_cdc_latency_ns']:.2f}ns latency")
    cdc_tb.log.info(f"Power efficiency: {power_stats['gated_percent']:.1f}% gated")
```

## Configuration Examples

### Clock Domain Scenarios

```python
# Fast source to slow destination (typical CPU to peripheral)
os.environ['clk_src_PERIOD_NS'] = '10'  # 100MHz
os.environ['clk_dst_PERIOD_NS'] = '50'  # 20MHz

# Slow source to fast destination (peripheral to CPU)
os.environ['clk_src_PERIOD_NS'] = '100' # 10MHz  
os.environ['clk_dst_PERIOD_NS'] = '5'   # 200MHz

# Same frequency (CDC for isolation)
os.environ['clk_src_PERIOD_NS'] = '20'  # 50MHz
os.environ['clk_dst_PERIOD_NS'] = '20'  # 50MHz
```

### Test Level Configuration

```python
# Quick verification (2-3 minutes)
os.environ['TEST_LEVEL'] = 'basic'

# Comprehensive verification (5-8 minutes)  
os.environ['TEST_LEVEL'] = 'medium'

# Exhaustive verification (15-25 minutes)
os.environ['TEST_LEVEL'] = 'full'
```

## Best Practices

1. **Start with conservative CDC configurations** before testing aggressive timing
2. **Monitor CDC latency** to ensure it meets design requirements
3. **Use CDC-specific randomization** rather than generic configurations
4. **Test both fast->slow and slow->fast** clock domain crossings
5. **Validate data integrity** with walking bits tests
6. **Combine with power monitoring** for realistic power analysis
7. **Use appropriate test levels** based on verification goals
8. **Document CDC timing requirements** and validate against them
9. **Test with realistic clock ratios** from your target system
10. **Monitor for timing violations** and metastability issues

## Integration Notes

- **Inherits from TBBase**: Provides logging, configuration, and common infrastructure
- **Uses GAXI components**: Leverages proven protocol components for CDC testing
- **FlexConfigGen integration**: Advanced randomization pattern generation
- **Memory model integration**: Shared memory for cross-domain data verification
- **Compatible with power monitoring**: Works with `amba_cg_ctrl.py` for power analysis
- **Environment variable configuration**: Flexible test setup without code changes

The `CDCHandshakeTB` class provides a comprehensive foundation for verifying clock domain crossing implementations, enabling teams to validate CDC functionality, timing, and performance while maintaining observability into cross-domain behavior.