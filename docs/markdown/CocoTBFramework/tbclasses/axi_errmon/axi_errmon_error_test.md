# AXI Error Monitor Error Test

## Overview

The `AXIErrorMonErrorTest` class implements specialized tests for error detection and reporting functionality of the AXI Error Monitor. It focuses on verifying timeout detection, error responses, and recovery after error conditions. This class inherits from the base test class and provides test scenarios that deliberately trigger different types of errors.

## Class Definition

```python
class AXIErrorMonErrorTest(AXIErrorMonBaseTest):
    """
    Error tests for AXI Error Monitor.
    Tests error detection, reporting, and recovery.
    """

    def __init__(self, tb):
        """
        Initialize with a reference to the testbench
        
        Args:
            tb: Reference to the AXIErrorMonitorTB wrapper class
        """
        super().__init__(tb)
```

## Key Features

- Address timeout detection testing
- Data timeout detection testing
- Response timeout detection testing (write mode only)
- Response error (SLVERR/DECERR) detection
- Timer behavior verification
- Edge case testing for transactions that complete just before timeout
- Recovery testing after error conditions

## Primary Methods

### run

Runs all error tests and reports results.

```python
async def run(self):
    """
    Run all error tests
    
    Returns:
        True if all tests passed, False otherwise
    """
    # Run timeout tests
    addr_timeout_passed = await self.test_addr_timeout()
    data_timeout_passed = await self.test_data_timeout()
    
    # Run response timeout test (write mode only)
    if not self.tb.is_read:
        resp_timeout_passed = await self.test_resp_timeout()
    else:
        resp_timeout_passed = True  # Skip for read mode
        
    # Run response error test
    resp_error_passed = await self.test_resp_error()
    
    # Run edge case completion test
    edge_case_passed = await self.test_edge_case_completion()
    
    # Run recovery test
    recovery_passed = await self.test_recovery_after_errors()
    
    # Report results
    all_passed = (
        addr_timeout_passed and
        data_timeout_passed and
        resp_timeout_passed and
        resp_error_passed and
        edge_case_passed and
        recovery_passed
    )
    
    return all_passed
```

### test_addr_timeout

Tests address timeout detection.

```python
async def test_addr_timeout(self):
    """
    Test address timeout detection
    
    This test verifies that the monitor correctly detects and reports
    timeout conditions in the address channel.
    
    Returns:
        True if test passed, False otherwise
    """
    # Reset and setup for clean test state
    await self.reset_and_setup_for_test()
    
    # Drive an address timeout scenario
    result = await self.drive_error_scenario(
        error_type='addr_timeout',
        addr=0x7000,
        id_value=0
    )
    
    # Check that error was detected with the correct type
    # ...
```

### test_data_timeout

Tests data timeout detection.

```python
async def test_data_timeout(self):
    """
    Test data timeout detection
    
    This test verifies that the monitor correctly detects and reports
    timeout conditions in the data channel.
    
    Returns:
        True if test passed, False otherwise
    """
    # Reset and setup for clean test state
    await self.reset_and_setup_for_test()
    
    # Drive a data timeout scenario
    result = await self.drive_error_scenario(
        error_type='data_timeout',
        addr=0x7100,
        id_value=1
    )
    
    # Check that error was detected with the correct type
    # ...
```

### test_resp_timeout

Tests response timeout detection (write mode only).

```python
async def test_resp_timeout(self):
    """
    Test response timeout detection (write mode only)
    
    This test verifies that the monitor correctly detects and reports
    timeout conditions in the response channel.
    
    Returns:
        True if test passed, False otherwise
    """
    # Skip for read mode
    if self.tb.is_read:
        self.log.info(f"Skipping response timeout test for read mode")
        return True
        
    # Reset and setup for clean test state
    await self.reset_and_setup_for_test()
    
    # Drive a response timeout scenario
    result = await self.drive_error_scenario(
        error_type='resp_timeout',
        addr=0x7200,
        id_value=2
    )
    
    # Check that error was detected with the correct type
    # ...
```

### test_resp_error

Tests response error detection.

```python
async def test_resp_error(self):
    """
    Test response error detection
    
    This test verifies that the monitor correctly detects and reports
    error responses (SLVERR/DECERR).
    
    Returns:
        True if test passed, False otherwise
    """
    # Reset and setup for clean test state
    await self.reset_and_setup_for_test()
    
    # Test both error types
    error_types = [
        (2, "SLVERR"),  # SLVERR = 2
        (3, "DECERR")   # DECERR = 3
    ]
    
    all_passed = True
    id_value = 0
    
    for error_code, error_name in error_types:
        # Drive a response error scenario
        result = await self.drive_error_scenario(
            error_type='resp_error',
            addr=0x7300 + (error_code * 0x100),
            id_value=id_value,
            resp_value=error_code
        )
        
        # Check that error was detected
        # ...
```

### test_timer_behavior

Tests timer initialization and counting behavior.

```python
async def test_timer_behavior(self):
    """
    Test timer behavior
    
    This test verifies the timer initialization and counting behavior,
    including the countdown from MAX value.
    
    Returns:
        True if test passed, False otherwise
    """
    # Test the timer countdown behavior
    result = await self.test_timer_countdown()
    
    # ...
```

## Test Methodology

The error test class follows a structured approach:

1. **Reset**: Clean state preparation before each test
2. **Error Scenario Generation**: Create specific conditions to trigger errors
3. **Error Detection Verification**: Check for correct error reports
4. **Error Information Validation**: Verify error type, ID, and address

For each error type, the test:
- Sets up specific conditions that should trigger the error
- Verifies the error is detected and reported correctly
- Checks that the error includes the correct information (type, ID, address)

## Implementation Notes

- Tests are structured to be independent of each other
- Each test resets the DUT for a clean state
- Error scenarios use the `drive_error_scenario` method from the base test class
- Timeout values are based on the configured timeouts plus a margin
- SLVERR (2) and DECERR (3) are both tested for response errors
- Write-specific tests are skipped in read mode

## Example Usage

```python
# Create AXI Error Monitor testbench
tb = AXIErrorMonitorTB(dut, ...)

# Create error test class
error_test = AXIErrorMonErrorTest(tb)

# Run all error tests
all_passed = await error_test.run()

# Or run individual tests
addr_timeout_passed = await error_test.test_addr_timeout()
resp_error_passed = await error_test.test_resp_error()
```

## See Also

- [AXI Error Monitor Base Test](axi_errmon_base_test.md) - Base test utilities
- [AXI Error Monitor FIFO Test](axi_errmon_fifo_test.md) - FIFO behavior tests

## Navigation

[↑ AXI Error Monitor Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
