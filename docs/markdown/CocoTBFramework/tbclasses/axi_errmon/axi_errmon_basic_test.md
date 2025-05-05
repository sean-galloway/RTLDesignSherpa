# AXI Error Monitor Basic Test

## Overview

The `AXIErrorMonBasicTest` class implements fundamental functionality tests for the AXI Error Monitor module. It focuses on verifying basic transaction handling, simple operational scenarios, and core features. This class inherits from the base test class and provides specialized tests for basic functionality.

## Class Definition

```python
class AXIErrorMonBasicTest(AXIErrorMonBaseTest):
    """
    Basic tests for AXI Error Monitor.
    Tests simple transaction handling and basic functionality.
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

- Verification of single transaction handling
- Sequential transaction testing
- Pipelined transaction testing (write mode)
- Timer reset verification
- Basic operational validation

## Primary Methods

### run

Runs all basic tests and reports results.

```python
async def run(self):
    """
    Run all basic tests
    
    Returns:
        True if all tests passed, False otherwise
    """
    # Reset the DUT
    await self.tb.reset_dut()
    
    # Run simple transaction tests
    single_passed = await self.test_single_transaction()
    
    # Run timer validation test
    timer_passed = await self.test_timer_reset()
    
    # Run sequential transactions test
    sequential_passed = await self.test_sequential_transactions()
    
    # Run pipelined transactions test
    pipeline_passed = await self.test_pipelined_transactions()
    
    # Report results
    all_passed = (single_passed and timer_passed and 
                 sequential_passed and pipeline_passed)
    
    return all_passed
```

### test_single_transaction

Tests that a single transaction can be processed correctly.

```python
async def test_single_transaction(self):
    """
    Test a single simple transaction
    
    This tests that a single transaction can be processed correctly
    without any errors or timeouts.
    
    Returns:
        True if test passed, False otherwise
    """
    # Clear any previous errors
    self.tb.errors_detected = []
    
    # Drive a single transaction
    transaction = await self.drive_basic_transaction(
        addr=0x1000,
        id_value=0,
        data_value=0xABCD1234,
        resp_value=0,  # OKAY
        control_ready=False,  # Use default ready behavior
        wait_for_completion=True
    )
    
    # Check for successful completion and no errors
    # ...
```

### test_sequential_transactions

Tests multiple sequential transactions.

```python
async def test_sequential_transactions(self):
    """
    Test multiple sequential transactions
    
    This tests that multiple sequential transactions can be processed correctly
    without any errors or timeouts.
    
    Returns:
        True if test passed, False otherwise
    """
    # Clear any previous errors
    self.tb.errors_detected = []
    
    # Drive multiple transactions sequentially
    num_transactions = 10
    
    for i in range(num_transactions):
        addr = 0x2000 + (i * 0x100)
        id_value = i % self.tb.channels
        data_value = 0xA0000000 | i
        
        transaction = await self.drive_basic_transaction(
            addr=addr,
            id_value=id_value,
            data_value=data_value,
            resp_value=0,  # OKAY
            control_ready=False,  # Use default ready behavior
            pipeline_phases=False,  # Sequential behavior
            wait_for_completion=True
        )
        
        # Check for successful completion
        # ...
```

### test_pipelined_transactions

Tests pipelined transactions (if supported).

```python
async def test_pipelined_transactions(self):
    """
    Test pipelined transactions (if supported)
    
    This tests that pipelined transactions (address and data phases
    running in parallel) can be processed correctly without any
    errors or timeouts.
    
    Returns:
        True if test passed, False otherwise
    """
    # Skip for read mode (doesn't support pipelining)
    if self.tb.is_read:
        self.log.info(f"Skipping pipelined transactions test for read mode")
        return True
        
    # Clear any previous errors
    self.tb.errors_detected = []
    
    # Drive multiple transactions with pipelining
    num_transactions = 10
    
    for i in range(num_transactions):
        addr = 0x3000 + (i * 0x100)
        id_value = i % self.tb.channels
        data_value = 0xB0000000 | i
        
        transaction = await self.drive_basic_transaction(
            addr=addr,
            id_value=id_value,
            data_value=data_value,
            resp_value=0,  # OKAY
            control_ready=False,  # Use default ready behavior
            pipeline_phases=True,  # Enable pipelining
            wait_for_completion=True
        )
        
        # Check for successful completion
        # ...
```

## Test Methodology

The basic test class follows a structured approach:

1. **Initialization**: Clear error flags and prepare test state
2. **Transaction Execution**: Send transactions with specific parameters
3. **Verification**: Check for completion without errors
4. **Result Reporting**: Log test outcome and return pass/fail status

The tests verify basic functionality in increasing complexity:
- Single transaction: Verifies fundamental operation
- Sequential transactions: Tests handling of multiple transactions
- Pipelined transactions: Tests parallel operation (write mode only)

## Implementation Notes

- Reset is performed before starting tests
- Error tracking is cleared for each test
- Transactions use different addresses to avoid interference
- IDs are assigned to distribute across channels (ID % channels)
- Skipping pipelined tests in read mode since it's not applicable
- All tests verify no errors are reported during normal operation

## Example Usage

```python
# Create AXI Error Monitor testbench
tb = AXIErrorMonitorTB(dut, ...)

# Create basic test class
basic_test = AXIErrorMonBasicTest(tb)

# Run all basic tests
all_passed = await basic_test.run()

# Or run individual tests
single_passed = await basic_test.test_single_transaction()
sequential_passed = await basic_test.test_sequential_transactions()
```

## See Also

- [AXI Error Monitor Base Test](axi_errmon_base_test.md) - Base test utilities
- [AXI Error Monitor Error Test](axi_errmon_error_test.md) - Error scenario tests

## Navigation

[↑ AXI Error Monitor Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
