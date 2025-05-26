# AXI Error Monitor Multichannel Test

## Overview

The `AXIErrorMonMultiChannelTest` class implements specialized tests focused on multi-channel operation of the AXI Error Monitor. It verifies channel independence, concurrent operation, and ID-based channel selection. This class inherits from the base test class and provides test scenarios specific to multi-channel configurations.

## Class Definition

```python
class AXIErrorMonMultiChannelTest(AXIErrorMonBaseTest):
    """
    Multi-channel tests for AXI Error Monitor.
    Tests channel independence and concurrent operation.
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

- Verification of concurrent transactions across channels
- Channel interference testing
- ID-based channel selection testing
- Multi-channel isolation verification
- Parallel transaction processing

## Primary Methods

### run

Runs all multi-channel tests and reports results.

```python
async def run(self):
    """
    Run all multi-channel tests
    
    Returns:
        True if all tests passed, False otherwise
    """
    # Skip for single channel configuration
    if self.tb.channels <= 1:
        self.log.info(f"Skipping multi-channel tests for single-channel configuration")
        return True
        
    # Reset the DUT
    await self.tb.reset_dut()
    
    # Run concurrent transactions test
    concurrent_passed = await self.test_concurrent_transactions()
    
    # Run channel interference test
    interference_passed = await self.test_channel_interference()
    
    # Run ID-based channel selection test
    id_selection_passed = await self.test_id_channel_selection()
    
    # Report results
    all_passed = (concurrent_passed and 
                  interference_passed and 
                  id_selection_passed)
    
    return all_passed
```

### test_concurrent_transactions

Tests concurrent transactions across multiple channels.

```python
async def test_concurrent_transactions(self):
    """
    Test concurrent transactions across multiple channels
    
    This test verifies that transactions on different channels can
    proceed concurrently, with adjustments for write mode's shared FIFO.
    
    Returns:
        True if test passed, False otherwise
    """
    # Reset and setup for clean test state
    await self.reset_and_setup_for_test()
    
    # For read mode, use the original approach with fully concurrent transactions
    if self.tb.is_read:
        # Launch transactions on all channels concurrently
        tasks = []
        num_channels = min(self.tb.channels, 4)  # Test up to 4 channels
        
        for ch in range(num_channels):
            addr = 0x8000 + (ch * 0x1000)
            
            # Use thread-safe method to launch tasks
            task = cocotb.start_soon(self.drive_basic_transaction(
                addr=addr,
                id_value=ch,
                data_value=0xC0000000 | ch,
                resp_value=0,  # OKAY
                control_ready=False,  # Use default ready behavior
                wait_for_completion=False
            ))
            tasks.append(task)
            
        # Wait for all tasks to complete
        for task in tasks:
            await task
            
        # Check for completed transactions
        # ...
    else:
        # For write mode with shared FIFO, we need to be more careful
        # Launch transactions sequentially, but process them concurrently
        # ...
```

### test_channel_interference

Tests that errors on one channel don't affect other channels.

```python
async def test_channel_interference(self):
    """
    Test that errors on one channel don't affect other channels
    
    This test verifies that error conditions on one channel
    don't interfere with transactions on other channels.
    
    Returns:
        True if test passed, False otherwise
    """
    # Reset and setup for clean test state
    await self.reset_and_setup_for_test()
    
    # Create an error condition on channel 0
    error_channel = 0
    normal_channel = 1 % self.tb.channels  # Use channel 1 (or 0 if channels=1)
    
    # Ensure we have different channels
    if normal_channel == error_channel:
        normal_channel = (error_channel + 1) % self.tb.channels
        
    # Implementation differs between read and write modes
    # ...
```

### test_id_channel_selection

Tests ID-based channel selection.

```python
async def test_id_channel_selection(self):
    """
    Test ID-based channel selection
    
    This test verifies that the monitor correctly selects channels
    based on transaction IDs.
    
    Returns:
        True if test passed, False otherwise
    """
    # Skip for AXI-Lite mode (doesn't use IDs for channel selection)
    if not self.tb.is_axi:
        self.log.info(f"Skipping ID-based channel selection test for AXI-Lite mode")
        return True
        
    # Reset and setup for clean test state
    await self.reset_and_setup_for_test()
    
    # Generate IDs that map to different channels
    id_values = []
    for ch in range(min(self.tb.channels, 4)):  # Test up to 4 channels
        # Create ID that maps to this channel (ID % channels == ch)
        id_value = ch + (self.tb.channels * ch)
        id_values.append(id_value)
        
    # Test ID-based selection in read or write mode
    # ...
```

## Test Methodology

The multi-channel test class follows a structured approach:

1. **Channel Selection**: Use ID values to target specific channels
2. **Parallel Operation**: Launch concurrent transactions on different channels
3. **Isolation Verification**: Check that channels operate independently
4. **Error Containment**: Verify errors in one channel don't affect others

The tests verify three core aspects of multi-channel operation:
- **Concurrent Operation**: All channels can process transactions simultaneously
- **Channel Isolation**: Errors and conditions in one channel don't affect others
- **ID-based Routing**: Transactions are correctly routed based on ID values

## Read vs. Write Mode Differences

### Read Mode
- Fully concurrent operation across channels
- Independent channels with separate resources
- Error conditions strictly isolated to the affected channel

### Write Mode
- Limited concurrency due to shared FIFO
- Sequential address phases but concurrent data/response phases
- Need to manage shared resource conflicts

## Implementation Notes

- Tests automatically adapt to the number of available channels
- Tests are skipped for single-channel configurations
- For write mode, concurrency is managed to avoid shared FIFO conflicts
- Channel selection uses the formula: channel = ID % channels
- Tests include error propagation checks between channels
- ID values are carefully selected to target specific channels

## Example Usage

```python
# Create AXI Error Monitor testbench with multiple channels
tb = AXIErrorMonitorTB(
    dut,
    addr_width=32,
    id_width=8,
    is_read=True,
    channels=4  # Multi-channel configuration
)

# Create multichannel test class
multichannel_test = AXIErrorMonMultiChannelTest(tb)

# Run all multichannel tests
all_passed = await multichannel_test.run()

# Or run individual tests
concurrent_passed = await multichannel_test.test_concurrent_transactions()
id_selection_passed = await multichannel_test.test_id_channel_selection()
```

## See Also

- [AXI Error Monitor Base Test](axi_errmon_base_test.md) - Base test utilities
- [AXI Error Monitor FIFO Test](axi_errmon_fifo_test.md) - FIFO behavior tests

## Navigation

[↑ AXI Error Monitor Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
