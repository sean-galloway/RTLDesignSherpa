# AXI Error Monitor Base Test

## Overview

The `AXIErrorMonBaseTest` class provides a foundation of common utilities and methods used by all specialized test classes in the AXI Error Monitor testbench. It implements core transaction handling, error scenario generation, and channel state tracking functionality.

## Class Definition

```python
class AXIErrorMonBaseTest:
    """
    Base class for AXI Error Monitor tests.
    Provides common utilities for all test classes.
    """

    def __init__(self, tb):
        """
        Initialize with a reference to the testbench
        
        Args:
            tb: Reference to the AXIErrorMonitorTB wrapper class
        """
```

## Key Features

- Transaction driving and tracking
- Error scenario generation
- Channel state management
- Transaction queuing and processing
- Timer behavior verification
- Transaction recovery testing

## Key Properties

```python
# Transaction tracking
self.active_transactions = {}
self.completed_transactions = []

# Per-channel state tracking
self.channel_states = [{'busy': False, 'last_tx_time': 0} for _ in range(self.tb.channels)]

# Transaction queue and processor state
self.transaction_queue = []
self.queue_processor_active = False

# Expected errors tracking
self.expected_errors = []
```

## Primary Methods

### drive_basic_transaction

Drives a complete AXI transaction through the DUT with configurable control over each phase.

```python
async def drive_basic_transaction(self,
                                addr=0x1000,
                                id_value=0,
                                data_value=0xCAFEBABE,
                                resp_value=0,
                                control_ready=False,
                                addr_ready_delay=0,
                                data_ready_delay=0,
                                resp_ready_delay=0,
                                pipeline_phases=True,
                                wait_for_completion=True,
                                wait_prev_completion=True):
    """
    Drive a complete AXI transaction through the DUT with full phase control.
    
    This method drives all phases of an AXI transaction (address, data, response)
    with configurable control over ready signal timing for each phase.
    Supports AXI parallelism where multiple channels can operate simultaneously.
    
    Args:
        addr: Address for the transaction
        id_value: ID for the transaction
        data_value: Data value for write transactions or read responses
        resp_value: Response code (0=OKAY, 1=EXOKAY, 2=SLVERR, 3=DECERR)
        control_ready: If True, use the ready delay parameters
        addr_ready_delay: Cycles to delay address ready
        data_ready_delay: Cycles to delay data ready
        resp_ready_delay: Cycles to delay response ready
        pipeline_phases: If True, enable AXI parallelism (AW/W in same cycle)
        wait_for_completion: If True, wait for all phases to complete
        wait_prev_completion: If True, wait for previous transactions on same channel
        
    Returns:
        Dict with transaction details and status
    """
```

### drive_error_scenario

Drives a transaction that will trigger a specific error condition.

```python
async def drive_error_scenario(self,
                               error_type,
                               addr=0x2000,
                               id_value=1,
                               data_value=0xDEADBEEF,
                               resp_value=0):
    """
    Drive a transaction that will trigger a specific error with improved waiting logic
    
    Args:
        error_type: Type of error to generate ('addr_timeout', 'data_timeout', 'resp_timeout', or 'resp_error')
        addr: Address for the transaction
        id_value: ID for the transaction
        data_value: Data value for write transactions or read responses
        resp_value: Response code (overridden for resp_error)
        
    Returns:
        True if error was detected, False otherwise
    """
```

### queue_transaction

Queues a transaction for sequential processing.

```python
async def queue_transaction(self, tx_params):
    """
    Queue a transaction and process in order
    
    Args:
        tx_params: Dictionary of parameters for drive_basic_transaction
        
    Returns:
        Transaction ID
    """
```

### reset_and_setup_for_test

Resets the DUT and sets up a clean test state.

```python
async def reset_and_setup_for_test(self):
    """Reset DUT and set up state for testing"""
```

### test_timer_countdown

Tests timer countdown behavior from maximum value to zero.

```python
async def test_timer_countdown(self):
    """
    Test the timer countdown behavior from MAX to 0
    
    This test verifies the timer architecture that initializes timers to MAX
    and counts down when active, rather than counting up from 0.
    
    Returns:
        True if test passed, False otherwise
    """
```

### test_multi_error_reporting

Tests error prioritization with multiple concurrent errors.

```python
async def test_multi_error_reporting(self):
    """
    Test error prioritization by forcing multiple error conditions simultaneously
    
    This test verifies the error prioritization logic that handles multiple
    concurrent errors and reports them in the correct order.
    
    Returns:
        True if test passed, False otherwise
    """
```

### test_timer_reset

Tests timer initialization and reset behavior.

```python
async def test_timer_reset(self):
    """
    Test timer reset from MAX to active count
    
    This test verifies the timer initialization to MAX and proper counting down
    when a transaction starts.
    
    Returns:
        True if test passed, False otherwise
    """
```

### test_edge_case_completion

Tests transaction completion just before timeout.

```python
async def test_edge_case_completion(self):
    """
    Test transaction completion just before timeout
    
    This test verifies that a transaction that completes just before
    the timeout threshold does not trigger an error.
    
    Returns:
        True if test passed, False otherwise
    """
```

### test_recovery_after_errors

Tests system recovery after various error conditions.

```python
async def test_recovery_after_errors(self):
    """
    Test system recovery after errors
    
    This test verifies that the system properly recovers after
    various error conditions and can process new transactions.
    
    Returns:
        True if test passed, False otherwise
    """
```

## Helper Methods

### _wait_for_channel_ready

Waits for a channel to be ready (not busy).

```python
async def _wait_for_channel_ready(self, ch_idx):
    """
    Wait for a channel to be ready (not busy)
    
    Args:
        ch_idx: Channel index to wait for
    """
```

### _complete_addr_phase

Completes the address phase of a transaction.

```python
async def _complete_addr_phase(self, tx_id, addr_packet):
    """
    Complete the address phase of a transaction
    
    Args:
        tx_id: Transaction ID to update
        addr_packet: Address packet to send
    """
```

### _complete_data_phase

Completes the data phase of a transaction.

```python
async def _complete_data_phase(self, tx_id, data_packet):
    """
    Complete the data phase of a transaction
    
    Args:
        tx_id: Transaction ID to update
        data_packet: Data packet to send
    """
```

### _complete_resp_phase

Completes the response phase of a transaction (write only).

```python
async def _complete_resp_phase(self, tx_id, resp_packet, wait_for_data=True):
    """
    Complete the response phase of a transaction (write only)
    
    Args:
        tx_id: Transaction ID to update
        resp_packet: Response packet to send
        wait_for_data: If True, wait for data phase to complete first
    """
```

### _check_for_expected_error

Checks if an expected error has been detected.

```python
def _check_for_expected_error(self, error_type, id_value, addr):
    """
    Check if the expected error has been detected
    
    Args:
        error_type: Type of error to check for
        id_value: Transaction ID
        addr: Transaction address
        
    Returns:
        True if error was detected, False otherwise
    """
```

## Example Usage

```python
# Create a basic transaction
transaction = await base_test.drive_basic_transaction(
    addr=0x1000,
    id_value=0,
    data_value=0xCAFEBABE,
    resp_value=0,  # OKAY
    control_ready=False,
    wait_for_completion=True
)

# Create an error scenario
error_detected = await base_test.drive_error_scenario(
    error_type='data_timeout',
    addr=0x2000,
    id_value=1
)

# Test timer behavior
timer_test_passed = await base_test.test_timer_countdown()

# Test recovery after errors
recovery_passed = await base_test.test_recovery_after_errors()
```

## See Also

- [AXI Error Monitor Base TB](axi_errmon_base_tb.md) - Main testbench wrapper
- [AXI Error Monitor Basic Test](axi_errmon_basic_test.md) - Basic functionality tests

## Navigation

[↑ AXI Error Monitor Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
