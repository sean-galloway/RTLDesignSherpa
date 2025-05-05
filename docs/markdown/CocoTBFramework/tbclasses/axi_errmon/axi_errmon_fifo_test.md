# AXI Error Monitor FIFO Test

## Overview

The `AXIErrorMonFIFOTest` class implements specialized tests focused on FIFO behavior in the AXI Error Monitor. It verifies FIFO filling, FIFO full conditions, channel isolation, and address tracking functionality. This class inherits from the base test class and provides test scenarios that exercise various FIFO capabilities.

## Class Definition

```python
class AXIErrorMonFIFOTest(AXIErrorMonBaseTest):
    """
    FIFO tests for AXI Error Monitor.
    Tests FIFO behavior, flow control, and address tracking.
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

- FIFO filling and buffer full detection
- Block ready signal assertion/deassertion
- Channel isolation in multi-channel configurations
- Error FIFO full condition handling
- Address tracking through FIFOs
- Shared FIFO behavior for write mode

## Primary Methods

### run

Runs all FIFO tests and reports results.

```python
async def run(self):
    """
    Run all FIFO tests
    
    Returns:
        True if all tests passed, False otherwise
    """
    # Reset the DUT
    await self.tb.reset_dut()
    
    # Run FIFO fill test
    fill_passed = await self.test_fifo_fill()
    
    # Run channel isolation test
    isolation_passed = await self.test_channel_isolation()
    
    # Run error FIFO full test
    error_fifo_passed = await self.test_error_fifo_full()
    
    # Run address tracking test
    addr_tracking_passed = await self.test_address_tracking()
    
    # Report results
    all_passed = (fill_passed and isolation_passed and 
                 error_fifo_passed and addr_tracking_passed)
    
    return all_passed
```

### test_fifo_fill

Tests FIFO filling and block_ready signal behavior.

```python
async def test_fifo_fill(self):
    """
    Test FIFO filling and block_ready signal
    
    This test fills the address FIFOs and verifies that the block_ready
    signal is asserted when FIFOs are full and deasserted when entries
    are removed.
    
    Returns:
        True if test passed, False otherwise
    """
    # Reset and setup for clean test state
    await self.reset_and_setup_for_test()
    
    # Calculate entries to fill each channel's FIFO
    entries_per_channel = self.tb.addr_fifo_depth
    
    # Drive FIFO fill test
    return await self.drive_fifo_fill_test(
        entries_per_channel=entries_per_channel
    )
```

### test_channel_isolation

Tests that channels are isolated and operate independently.

```python
async def test_channel_isolation(self):
    """
    Test that channels are isolated and operate independently
    
    This test verifies that filling one channel's FIFO does not affect other channels,
    with updated behavior for write mode where a single shared FIFO is used for the
    write data phase.
    
    Returns:
        True if test passed, False otherwise
    """
    # Skip for single channel configuration
    if self.tb.channels <= 1:
        self.log.info(f"Skipping channel isolation test for single-channel configuration")
        return True
        
    # Test logic varies between read mode (independent FIFOs)
    # and write mode (shared FIFO)
    # ...
```

### test_error_fifo_full

Tests error reporting when error FIFO is full.

```python
async def test_error_fifo_full(self):
    """
    Test error reporting when error FIFO is full
    
    This test verifies the error storing and prioritization logic when
    the error FIFO is full and cannot accept new errors.
    
    Returns:
        True if test passed, False otherwise
    """
    # Reset and set up for clean test state
    await self.reset_and_setup_for_test()
    
    # Clear any previous errors
    self.tb.errors_detected = []
    
    # Force error_ready low to simulate full FIFO
    self.tb.error_slave.set_randomizer(FlexRandomizer(self.tb.randomizer_configs['slow_consumer']))
    
    # Generate error scenarios with FIFO full
    # ...
```

### test_address_tracking

Tests address tracking through FIFOs.

```python
async def test_address_tracking(self):
    """
    Test address tracking through FIFOs
    
    This test verifies that addresses are correctly tracked through
    the FIFOs by filling them with transactions and checking that
    response errors report the correct addresses and IDs.
    
    Returns:
        True if test passed, False otherwise
    """
    # Reset and setup for clean test state
    await self.reset_and_setup_for_test()
    
    # Create list to hold all transactions
    all_transactions = []
    
    # Number of channels to test
    num_channels = min(self.tb.channels, 4)  # Test up to 4 channels
    
    # Create fifo_depth-1 transactions for each ID
    for id_value in range(num_channels):
        entries = self.tb.addr_fifo_depth - 1 if self.tb.is_read else 1
        addr_packets = self.create_nm1_transactions(id_value=id_value, entries=entries)
        
        # Add to transaction list
        all_transactions.extend(addr_packets)
    
    # Shuffle transactions and test address tracking
    # ...
```

### drive_fifo_fill_test

Implementation of FIFO fill testing with direct signal control.

```python
async def drive_fifo_fill_test(self, entries_per_channel=None):
    """
    Fill FIFOs to test block_ready assertion with direct signal control
    
    Updated to handle the new single shared FIFO for write data phase.
    For write mode, block_ready will assert when the single shared FIFO is full,
    regardless of channel ID.
    """
    # Use full FIFO depth if entries_per_channel is not specified
    if entries_per_channel is None:
        entries_per_channel = self.tb.addr_fifo_depth
        
    # Implementation differs between read and write mode
    # ...
```

### create_nm1_transactions

Creates N-1 transactions for a specific ID.

```python
def create_nm1_transactions(self,
                           addr=0x1000,
                           id_value=0,
                           entries=3):
    """
    Create N-1 transactions for a specific ID
    
    Args:
        addr: Base address
        id_value: ID value
        entries: Number of entries to create
        
    Returns:
        List of address packets
    """
```

## Test Methodology

The FIFO test class follows a structured approach:

1. **Reset**: Clean state preparation before each test
2. **FIFO Filling**: Send transactions to fill FIFOs
3. **Signal Monitoring**: Verify block_ready assertion/deassertion
4. **Behavior Verification**: Check that FIFOs behave correctly when full/empty

Key test aspects include:
- Testing different operational modes (read vs. write)
- Testing multi-channel isolation
- Testing error reporting with full error FIFO
- Testing address tracking through transaction FIFOs

## Behavior Differences Between Read and Write Modes

### Read Mode
- Each channel has an independent FIFO
- Filling one channel's FIFO doesn't affect others
- block_ready asserts when current channel's FIFO is full

### Write Mode
- Single shared FIFO for data phase
- Filling the shared FIFO affects all channels
- block_ready asserts when shared FIFO is full, regardless of channel

## Implementation Notes

- Tests adapt to the DUT configuration (read/write mode, channels)
- Different signal patterns are used for read vs. write mode
- Channel isolation testing skipped for single-channel configurations
- Randomized transaction ordering tests address tracking
- Error FIFO test verifies internal error storage and reporting

## Example Usage

```python
# Create AXI Error Monitor testbench
tb = AXIErrorMonitorTB(dut, ...)

# Create FIFO test class
fifo_test = AXIErrorMonFIFOTest(tb)

# Run all FIFO tests
all_passed = await fifo_test.run()

# Or run individual tests
fill_passed = await fifo_test.test_fifo_fill()
addr_tracking_passed = await fifo_test.test_address_tracking()
```

## See Also

- [AXI Error Monitor Base Test](axi_errmon_base_test.md) - Base test utilities
- [AXI Error Monitor Error Test](axi_errmon_error_test.md) - Error scenario tests

## Navigation

[↑ AXI Error Monitor Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
