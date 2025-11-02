# CocoTBFramework Testing Modules Overview

## Framework Philosophy

The CocoTBFramework testing modules are designed around the principle of **comprehensive, reusable, and scalable verification**. Each module provides a complete testing ecosystem for specific digital circuit components, built on top of a robust base class that ensures safety, reliability, and detailed reporting.

## Architecture

### Base Class Foundation
All testing modules inherit from `TBBase` which provides:
- **Safety monitoring**: Timeout protection, memory limits, progress tracking
- **Resource management**: CPU and task monitoring, graceful shutdown
- **Logging infrastructure**: Comprehensive logging with configurable levels
- **Common utilities**: Type conversion, time management, signal monitoring

### Modular Design
Each testing module follows a consistent pattern:
- **Initialization**: Parameter extraction from environment variables
- **Test suites**: Multiple test methods for different scenarios
- **Comprehensive testing**: Configurable test levels (basic/medium/full)
- **Detailed reporting**: Pass/fail statistics with failure analysis

## Key Features

### 1. Multi-Level Testing
Each module supports three test levels:
- **Basic**: Essential functionality tests, minimal test vectors
- **Medium**: Extended testing with additional patterns
- **Full**: Comprehensive testing including edge cases and stress tests

### 2. Intelligent Test Vector Generation
- **Exhaustive testing**: For small parameter spaces
- **Statistical sampling**: For large parameter spaces
- **Pattern-based testing**: Walking ones, alternating patterns, corner cases
- **Architecture-specific tests**: Tailored to specific implementation details

### 3. Comprehensive Error Analysis
- **Detailed failure reporting**: Binary comparisons, expected vs actual values
- **Pattern analysis**: Bit-by-bit breakdowns for debugging
- **Statistical summaries**: Pass/fail counts and failure categorization

### 4. Environment-Driven Configuration
All modules use environment variables for configuration:
- `PARAM_*`: Circuit parameters (width, depth, polynomial, etc.)
- `TEST_LEVEL`: Test intensity (basic/medium/full)
- `SEED`: Random number generator seed for reproducibility
- `DUT`: Device under test identifier

## Module-Specific Features

### Arithmetic Modules (Adder, Subtractor, Multiplier, Divider)
- **Carry/borrow propagation testing**: Ensures proper bit-level interactions
- **Boundary condition testing**: Zero, maximum values, overflow conditions
- **Algorithm-specific testing**: Booth multiplier patterns, carry-save adder validation

### Memory Modules (CAM)
- **State management**: Empty, full, partially filled states
- **Tag operations**: Valid/invalid marking, status checking
- **Capacity testing**: Maximum depth validation

### Protocol Modules (CRC)
- **Standard compliance**: Support for multiple CRC standards
- **Parameter validation**: Polynomial, initial value, reflection settings
- **Data pattern testing**: Various data patterns to stress CRC calculations

## Usage Patterns

### Basic Usage
```python
@cocotb.test()
async def test_basic(dut):
    tb = AdderTB(dut)
    await tb.run_comprehensive_tests()
```

### Advanced Configuration
```python
@cocotb.test()
async def test_advanced(dut):
    # Configure through environment or constructor
    safety_limits = {'max_test_duration_minutes': 60}
    tb = MultiplierTB(dut, safety_limits)
    
    # Print configuration
    tb.print_settings()
    
    # Run specific test suites
    await tb.main_loop(count=1000)
    await tb.booth_specific_test()
    await tb.corner_cases_test()
```

### Custom Test Integration
```python
@cocotb.test()
async def test_custom(dut):
    tb = CRCTB(dut, rnd_count=500)
    
    # Generate custom test data
    tb.generate_test_data()
    
    # Run tests
    await tb.main_loop()
    
    # Access results
    tb.log.info(f"Tests passed: {tb.pass_count}/{tb.test_count}")
```

## Best Practices

### 1. Environment Setup
Set appropriate environment variables before running tests:
```bash
export PARAM_N=8
export TEST_LEVEL=medium
export SEED=42
export LOG_PATH=/path/to/logs/test.log
```

### 2. Test Level Selection
- Use **basic** for quick functionality verification
- Use **medium** for standard validation
- Use **full** for comprehensive verification before tape-out

### 3. Safety Configuration
Adjust safety limits based on test requirements:
```python
safety_limits = {
    'max_test_duration_minutes': 30,
    'max_memory_mb': 4096,
    'progress_timeout_minutes': 10
}
```

### 4. Logging and Debug
- Enable detailed logging for debugging: `TBBase.default_log_level = logging.DEBUG`
- Use progress markers for long-running tests
- Review failure summaries for systematic issues

## Integration with Cocotb

The framework integrates seamlessly with cocotb:
- **Async/await support**: All test methods are async-compatible
- **Signal handling**: Direct DUT signal manipulation
- **Timing control**: Built-in clock and timing utilities
- **Error propagation**: Assertion failures stop test execution

## Extensibility

The framework is designed for easy extension:

### Adding New Test Patterns
```python
async def custom_test_pattern(self):
    for test_case in custom_test_cases:
        # Apply inputs
        # Wait for settling
        # Verify outputs
        # Track statistics
```

### Custom Verification Logic
```python
def custom_verify(self, inputs, outputs):
    # Custom verification logic
    # Return pass/fail status
    # Generate detailed error messages
```

### Architecture-Specific Extensions
Each module can be extended for specific implementations:
```python
class BoothMultiplierTB(MultiplierTB):
    async def booth_radix4_test(self):
        # Booth-specific test patterns
```

## Performance Considerations

### Test Vector Optimization
- Automatic exhaustive vs. sampling selection based on parameter space size
- Stratified sampling for large parameter spaces
- Early termination on systematic failures

### Memory Management
- Built-in memory monitoring and limits
- Automatic cleanup of test data structures
- Progress tracking to prevent infinite loops

### Parallel Execution
- Support for concurrent test execution
- Task monitoring and limits
- Resource utilization tracking

This framework provides a solid foundation for comprehensive digital circuit verification, combining ease of use with powerful testing capabilities and detailed analysis tools.