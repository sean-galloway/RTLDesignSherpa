# AXI Error Monitor Ready Controller

## Overview

The `ReadySignalController` class provides centralized control for all ready signals in the AXI Error Monitor testbench. It serves as a single point of control for manipulating ready signals, tracking signal transitions, and handling special conditions like the block_ready signal, which is essential for creating various test scenarios and simulating backpressure.

## Class Definition

```python
class ReadySignalController:
    """
    Enhanced centralized controller for AXI ready signals.
    
    This class provides a single point of control for all ready signals in the AXI interface.
    It handles special conditions like o_block_ready assertion and provides timing control
    for ready signal delays.
    
    Key features:
    - Single point of control for all ready signals
    - Automatic handling of o_block_ready to i_ready relationship
    - Methods for forcing ready signals low for specific durations
    - Event tracking and logging
    """

    def __init__(self, dut, log=None):
        """
        Initialize the controller with the DUT and optional logger
        
        Args:
            dut: Device under test
            log: Optional logger for event tracking
        """
```

## Key Features

- Centralized control of all AXI ready signals
- Automatic handling of block_ready to ready relationship
- Signal delay control with configurable timing
- Event tracking for verification
- Coordinated reset and state management
- Support for forced signal assertion/deassertion

## Key Properties

```python
# Default ready states (typically asserted for good throughput)
self.default_i_ready = 1
self.default_i_data_ready = 1
self.default_i_resp_ready = 1

# Current states
self.i_ready_forced_low = False
self.i_data_ready_forced_low = False
self.i_resp_ready_forced_low = False

# Block ready state
self.block_ready_asserted = False

# Monitor tasks
self.monitor_tasks = []
self.delay_tasks = {}

# Events for tracking
self.block_ready_events = []
```

## Primary Methods

### start

Starts the controller and monitoring tasks.

```python
async def start(self):
    """
    Start the controller and monitoring tasks
    
    This initiates monitoring of the o_block_ready signal and applies
    initial ready signal values.
    """
    # First stop any existing monitors to avoid duplicates
    await self.stop()
    
    # Start block_ready monitor
    task = cocotb.start_soon(self._monitor_block_ready())
    self.monitor_tasks.append(task)
    
    # Apply initial values
    self.apply_ready_values()
```

### stop

Stops all monitoring tasks.

```python
async def stop(self):
    """
    Stop all monitoring tasks
    
    This cleanly terminates all monitoring tasks started by the controller.
    """
    for task in self.monitor_tasks:
        task.kill()
    self.monitor_tasks = []
    
    # Kill any active delay tasks
    for task_id, task in self.delay_tasks.items():
        task.kill()
    self.delay_tasks = {}
```

### apply_ready_values

Applies current ready values to DUT signals.

```python
def apply_ready_values(self):
    """
    Apply the current ready values to the DUT signals
    
    This applies the current state of all ready signals, taking into account
    forced values and the block_ready state.
    """
    # For address channel ready (i_ready)
    # Special case: i_ready is forced low by o_block_ready
    if self.block_ready_asserted or self.i_ready_forced_low:
        self.dut.i_ready.value = 0
    else:
        self.dut.i_ready.value = self.default_i_ready
    
    # For other ready signals
    if not self.i_data_ready_forced_low:
        self.dut.i_data_ready.value = self.default_i_data_ready
    
    if not self.i_resp_ready_forced_low:
        self.dut.i_resp_ready.value = self.default_i_resp_ready
```

### Set Signal Methods

Methods for setting individual ready signals.

```python
def set_addr_ready(self, value):
    """Set the address channel ready signal (i_ready)"""
    
def set_data_ready(self, value):
    """Set the data channel ready signal (i_data_ready)"""
    
def set_resp_ready(self, value):
    """Set the response channel ready signal (i_resp_ready)"""
```

### Force Signal Methods

Methods for forcing ready signals low.

```python
def force_addr_ready_low(self, forced=True):
    """Force the address ready signal low regardless of default state"""
    
def force_data_ready_low(self, forced=True):
    """Force the data ready signal low regardless of default state"""
    
def force_resp_ready_low(self, forced=True):
    """Force the response ready signal low regardless of default state"""
```

### Delay Signal Methods

Methods for delaying ready signals.

```python
async def delay_addr_ready(self, cycles):
    """
    Delay address ready signal by specific number of clock cycles
    
    This forces the address ready signal low for the specified number of cycles
    and then automatically restores it.
    
    Args:
        cycles: Number of clock cycles to delay ready signal
        
    Returns:
        Task ID for tracking
    """
    
async def delay_data_ready(self, cycles):
    """Delay data ready signal by specific number of clock cycles"""
    
async def delay_resp_ready(self, cycles):
    """Delay response ready signal by specific number of clock cycles"""
```

### cancel_delay

Cancels a previously scheduled delay.

```python
def cancel_delay(self, task_id):
    """
    Cancel a previously scheduled ready signal delay
    
    Args:
        task_id: Task ID returned from delay_* method
        
    Returns:
        True if task was found and cancelled, False otherwise
    """
```

## Block Ready Monitoring

The controller automatically monitors the block_ready signal and adjusts the ready signals accordingly.

```python
async def _monitor_block_ready(self):
    """
    Monitor o_block_ready and control i_ready accordingly
    
    This is the core functionality that ensures i_ready is deasserted
    whenever o_block_ready is asserted.
    """
    try:
        while True:
            # Wait for o_block_ready to change
            await Edge(self.dut.o_block_ready)
            
            # Record block_ready events
            current_time = cocotb.utils.get_sim_time('ns')
            event = {
                'time': current_time,
                'value': self.dut.o_block_ready.value
            }
            self.block_ready_events.append(event)
            
            # Update block_ready state
            self.block_ready_asserted = bool(self.dut.o_block_ready.value)
            
            if self.dut.o_block_ready.value:
                # o_block_ready asserted, must force i_ready low
                self.dut.i_ready.value = 0
            elif not self.i_ready_forced_low:
                self.dut.i_ready.value = self.default_i_ready
                
    except Exception as e:
        if self.log:
            self.log.error(f"Error in block_ready monitor: {str(e)}")
```

## Event Tracking

The controller tracks block_ready events for verification and debugging.

```python
def clear_block_ready_events(self):
    """Clear the history of block_ready events"""
    
def get_block_ready_state(self):
    """Get current state of block_ready signal"""
    
def get_block_ready_events(self):
    """Get list of block_ready events"""
```

## Example Usage

```python
# Create ready controller
ready_ctrl = ReadySignalController(dut, log=dut._log)

# Start the controller
await ready_ctrl.start()

# Set ready signals
ready_ctrl.set_addr_ready(1)
ready_ctrl.set_data_ready(1)
ready_ctrl.set_resp_ready(1)

# Force data_ready low
ready_ctrl.force_data_ready_low(True)

# Delay addr_ready by 10 cycles
task_id = await ready_ctrl.delay_addr_ready(10)

# Check if block_ready is asserted
if ready_ctrl.get_block_ready_state():
    print("Block ready is asserted!")

# Stop the controller
await ready_ctrl.stop()
```

## Delay Task Implementation

Delay tasks are implemented as coroutines that force a signal low for a specific number of cycles, then restore it.

```python
async def _delay_task():
    # Wait for specified cycles
    for _ in range(cycles):
        await RisingEdge(self.dut.aclk)
    
    # Release the forced-low state if still in this delay
    if self.delay_tasks.get(task_id) is not None:
        self.force_addr_ready_low(False)
        
        # Remove task from tracking
        if task_id in self.delay_tasks:
            del self.delay_tasks[task_id]
```

## Implementation Notes

- The controller provides a clean API for test classes to manipulate ready signals
- block_ready signal has highest priority and forces i_ready low
- Delay tasks can be tracked and cancelled if needed
- Events are recorded with simulation timestamps
- Exception handling ensures robust operation
- All signals are properly restored after forced conditions

## See Also

- [AXI Error Monitor Base TB](axi_errmon_base_tb.md) - Main testbench wrapper
- [AXI Error Monitor Base Test](axi_errmon_base_test.md) - Base test utilities

## Navigation

[↑ AXI Error Monitor Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
