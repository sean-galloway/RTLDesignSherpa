# Common Test Classes Overview

## Introduction

The Common Test Classes in the CocoTBFramework provide standardized verification components for frequently used digital logic blocks. They establish consistent patterns for test organization, parameter handling, statistics tracking, and result reporting. Following these patterns ensures consistent verification across components and simplifies test creation.

## Core Design Patterns

### Class Structure

All common test classes follow a similar structure:

1. **Initialization**: Parse and validate parameters, setup the test environment
2. **Configuration**: Establish test settings, parameters, and options
3. **Test Methods**: Implement specific test scenarios
4. **Comprehensive Test**: Combine individual tests based on test level
5. **Reporting**: Track and report test statistics and results

### Standard Method Sets

Common test classes typically include these method categories:

- **Setup Methods**: `__init__`, `print_settings`, `clear_interface`
- **Control Methods**: `assert_reset`, `deassert_reset`
- **Core Test Methods**: `main_loop`, component-specific test methods
- **Comprehensive Test**: `run_comprehensive_tests`
- **Utility Methods**: Component-specific support functions

### Parameter Handling

The standard approach for handling parameters:

```python
def __init__(self, dut):
    TBBase.__init__(self, dut)
    # Gather the settings from the Parameters
    self.param_name = self.convert_to_int(os.environ.get('PARAM_NAME', 'default_value'))
    # Initialize test parameters
    self.test_level = os.environ.get('TEST_LEVEL', 'basic')
    self.seed = self.convert_to_int(os.environ.get('SEED', '12345'))
    # Use parameters to derive other settings
    self.max_val = 2**self.param_name
    self.mask = self.max_val - 1
    # Initialize random generator
    random.seed(self.seed)
    # Track test statistics
    self.test_count = 0
    self.pass_count = 0
    self.fail_count = 0
```

## Implementation Patterns

### Test Level Implementation

The pattern for implementing test levels:

```python
async def run_comprehensive_tests(self):
    """Run a comprehensive suite of tests based on test_level"""
    self.log.info(f"Running comprehensive tests at {self.test_level} level")
    
    # Clear the interface
    await self.clear_interface()
    
    # Determine test count based on level
    if self.test_level == 'basic':
        count = min(64, 2**self.N)
    elif self.test_level == 'medium':
        count = min(128, 2**self.N)
    else:  # 'full' or anything else
        count = min(256, 2**self.N)
    
    # Always run the main loop for standard tests
    await self.main_loop(count)
    
    # For medium and full test levels, add additional tests
    if self.test_level in ['medium', 'full']:
        await self.additional_test()
    
    # For full test level, add even more tests
    if self.test_level == 'full':
        await self.comprehensive_test()
    
    # Print final test summary
    self.log.info(f"Test Summary: {self.pass_count}/{self.test_count} passed, {self.fail_count} failed")
```

### Statistics Tracking

The pattern for tracking test statistics:

```python
# In test methods:
if condition_passed:
    self.pass_count += 1
else:
    self.log.error(f"Test failed: ...")
    self.fail_count += 1
    assert False, f"Test failed: ..."
    
self.test_count += 1
```

### Test Case Generation

The pattern for test case generation:

```python
# Determine if we need to test all possible values or random sampling
if self.max_val < count:
    self.log.info(f"Testing all {self.max_val} possible values")
    test_values = list(range(self.max_val))
else:
    self.log.info(f"Random sampling with {count} test vectors")
    test_values = [random.randint(0, self.mask) for _ in range(count)]
```

## Creating a New Common Test Class

To create a new common test class, follow these steps:

1. **Extend TBBase**:
   ```python
   class MyComponentTB(TBBase):
       def __init__(self, dut):
           TBBase.__init__(self, dut)
           # Component-specific initialization
   ```

2. **Parse Parameters**:
   ```python
   # Get parameters from environment
   self.PARAM_NAME = self.convert_to_int(os.environ.get('PARAM_NAME', 'default'))
   ```

3. **Create Test Methods**:
   ```python
   async def test_specific_feature(self):
       """Test component-specific functionality"""
       # Implementation...
   ```

4. **Implement Main Loop**:
   ```python
   async def main_loop(self, count):
       """Main test loop for standard testing"""
       # Implementation...
   ```

5. **Create Comprehensive Test**:
   ```python
   async def run_comprehensive_tests(self):
       """Run tests based on test_level"""
       # Implementation...
   ```

## Example Implementation

Here's a simple example of a new common test class:

```python
class CounterTB(TBBase):
    def __init__(self, dut):
        TBBase.__init__(self, dut)
        # Parse parameters
        self.WIDTH = self.convert_to_int(os.environ.get('PARAM_WIDTH', '8'))
        self.MAX_VAL = 2**self.WIDTH - 1
        self.test_level = os.environ.get('TEST_LEVEL', 'basic')
        
        # Initialize statistics
        self.test_count = 0
        self.pass_count = 0
        self.fail_count = 0
    
    async def test_increment(self):
        """Test counter increment functionality"""
        # Implementation...
    
    async def test_overflow(self):
        """Test counter overflow behavior"""
        # Implementation...
    
    async def main_loop(self, count):
        """Main test loop for standard testing"""
        # Implementation...
    
    async def run_comprehensive_tests(self):
        """Run a comprehensive suite of tests based on test_level"""
        # Implementation based on test levels...
```

## Best Practices

1. **Clear Documentation**: Document all parameters, test methods, and expected behavior
2. **Consistent Naming**: Follow established naming conventions
3. **Parameter Flexibility**: Support reasonable defaults for all parameters
4. **Error Reporting**: Provide detailed error messages with expected vs. actual values
5. **Test Independence**: Individual tests should be independent and not rely on state from previous tests
6. **Binary Representation**: Include binary representations in error messages for digital components
7. **Corner Cases**: Always test edge cases like zero, maximum values, and alternating bits
8. **Comprehensive Testing**: Implement run_comprehensive_tests with proper test level scaling

## Usage Guidelines

### Setting Parameters

Test environment parameters are set via environment variables:

```bash
PARAM_NAME=8 TEST_LEVEL=medium SEED=42 sim_build/simulator
```

### Controlling Test Level

The test level controls the thoroughness and execution time:

```python
# Use basic level for fast iteration
await tb.run_comprehensive_tests()  # Uses TEST_LEVEL from environment

# Force a specific level
tb.test_level = 'full'
await tb.run_comprehensive_tests()
```

### Running Specific Tests

For debugging, run specific tests instead of the comprehensive suite:

```python
# Run only a specific test
await tb.test_specific_feature()

# Run main loop with custom count
await tb.main_loop(count=10)
```

## See Also

- [TBBase](../tbbase.md) - Base class for all testbench components
- [Utilities](../utilities.md) - Common utility functions

## Navigation

[↑ Common Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
