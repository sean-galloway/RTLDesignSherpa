# AXI Error Monitor Base TB

## Overview

The `AXIErrorMonitorTB` class serves as the main wrapper for the AXI Error Monitor testbench environment. It integrates all the components needed for testing AXI protocol error detection, including masters, slaves, monitors, and test classes.

## Class Definition

```python
class AXIErrorMonitorTB(TBBase):
    """
    Wrapper class for AXI Error Monitor testbench.
    Manages masters, slaves, monitors, and provides interface to test classes.
    """

    def __init__(self, dut,
                addr_width=32,
                id_width=8,
                is_read=True,
                is_axi=True,
                timer_width=20,
                timeout_addr=1000,
                timeout_data=1000,
                timeout_resp=1000,
                error_fifo_depth=4,
                addr_fifo_depth=4,
                channels=1):
        """Initialize with DUT and configuration parameters"""
```

## Key Features

- Configurable address and ID widths
- Support for both read and write modes
- Configurable timer width and timeout values
- Support for multiple channels
- Integration of AXI protocol components with error monitoring
- Centralized error tracking and reporting

## Key Components

### GAXI Components

The class initializes and manages several GAXI components:

- **Address Master**: Controls address channel signals
- **Data Master**: Controls data channel signals
- **Response Master**: Controls response channel signals (write mode only)
- **Error Slave**: Receives error reports from DUT
- **Channel Monitors**: Monitor each channel for protocol conformance

```python
def _init_gaxi_components(self):
    """Initialize all GAXI components"""
    # Create address channel master
    self.addr_master = GAXIMaster(...)
    
    # Create data channel master
    self.data_master = GAXIMaster(...)
    
    # Create response channel master (write only)
    self.resp_master = None
    if not self.is_read:
        self.resp_master = GAXIMaster(...)
        
    # Create error reporting FIFO slave
    self.error_slave = GAXISlave(...)
    
    # Create monitors
    self.addr_monitor = GAXIMonitor(...)
    self.data_monitor = GAXIMonitor(...)
    self.resp_monitor = None
    # ...
```

### Field Configurations

The class creates field configurations for all channels and error reporting:

```python
def _create_field_configs(self):
    """Create field configurations for all channels"""
    self.addr_field_config = self._create_addr_field_config()
    self.data_field_config = self._create_data_field_config()
    self.resp_field_config = None if self.is_read else self._create_resp_field_config()
    self.error_field_config = self._create_error_field_config()
```

### Test Classes

The class instantiates and manages test classes for different aspects of verification:

```python
def _create_test_classes(self):
    """Create the test classes"""
    self.basic_test = AXIErrorMonBasicTest(self)
    self.fifo_test = AXIErrorMonFIFOTest(self)
    self.error_test = AXIErrorMonErrorTest(self)
    self.multichannel_test = AXIErrorMonMultiChannelTest(self)
    self.random_test = AXIErrorMonRandomTest(self)
```

## Error Constants

The class defines constants for error types that match RTL definitions:

```python
# Constants for error types (must match RTL definitions)
self.ERROR_ADDR_TIMEOUT = 0x1  # Address timeout
self.ERROR_DATA_TIMEOUT = 0x2  # Data timeout
self.ERROR_RESP_TIMEOUT = 0x4  # Response timeout
self.ERROR_RESP_ERROR = 0x8    # Response error
```

## Primary Methods

### reset_dut

Resets the DUT and all testbench components.

```python
async def reset_dut(self):
    """Reset the DUT and all testbench components"""
    # Reset the DUT
    self.dut.aresetn.value = 0
    
    # Reset monitoring structures
    self.errors_detected = []
    self.axi_transactions = []
    
    # Wait for reset to stabilize
    await self.wait_clocks('aclk', 5)
    
    # Release reset
    self.dut.aresetn.value = 1
    
    # Reset GAXI components
    # ...
```

### run_all_tests

Runs all test classes according to specified test level.

```python
async def run_all_tests(self, test_level='basic'):
    """
    Run all tests according to the test level
    
    Args:
        test_level: Test level ('basic', 'medium', or 'full')
        
    Returns:
        True if all tests passed, False otherwise
    """
    # Run basic tests
    basic_passed = await self.basic_test.run()
    fifo_passed = await self.fifo_test.run()
    
    # Medium adds error detection
    if test_level != 'basic':
        error_passed = await self.error_test.run()
        # ...
        
    # Full adds multichannel test
    if test_level == 'full':
        # ...
```

### set_data_resp

Sets the response code for read transactions.

```python
def set_data_resp(self, resp_value):
    """
    Set the i_data_resp signal value for read transactions.
    
    Args:
        resp_value: Response code (0-3)
            0: OKAY
            1: EXOKAY (exclusive access OK)
            2: SLVERR (slave error)
            3: DECERR (decode error)
    """
```

### verify_timer_operation

Verifies timer operation matches expected behavior.

```python
def verify_timer_operation(self, timer_operation):
    """
    Verify timer operation type matches the expected behavior
    
    Args:
        timer_operation: Expected timer operation ('count_up' or 'count_down')
        
    Returns:
        True if the operation is as expected, False otherwise
    """
```

## Error Callback

The class registers a callback function to process error reports:

```python
def _on_error_report(self, packet):
    """Callback for error reports from the error FIFO"""
    # Extract error information
    error_info = {
        'time': get_sim_time('ns'),
        'type': packet.error_type,
        'id': packet.error_id,
        'addr': packet.error_addr
    }
    
    # Add decoded error type string
    error_type_str = []
    if error_info['type'] & self.ERROR_ADDR_TIMEOUT:
        error_type_str.append("ADDR_TIMEOUT")
    # ...
    
    # Store error
    self.errors_detected.append(error_info)
```

## Example Usage

```python
# Create testbench
tb = AXIErrorMonitorTB(
    dut,
    addr_width=32,
    id_width=8,
    is_read=True,
    timer_width=20,
    timeout_addr=1000,
    timeout_data=1000,
    timeout_resp=1000,
    channels=1
)

# Run tests
await tb.reset_dut()
all_passed = await tb.run_all_tests(test_level="medium")

# Check errors
for error in tb.errors_detected:
    print(f"Error detected: {error['type_str']}")
```

## See Also

- [AXI Error Monitor Base Test](axi_errmon_base_test.md) - Base test utilities
- [AXI Error Monitor Ready Controller](axi_errmon_readyctrl.md) - Ready signal controller

## Navigation

[↑ AXI Error Monitor Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
