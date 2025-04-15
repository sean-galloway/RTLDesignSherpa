# TBBase Class Documentation

## Overview
`TBBase` is the core base class for testbenches in the CocoTB verification framework. It provides essential functionality for setting up and managing testbenches, including:

- Logging configuration and management
- Clock generation and control
- Reset assertion and deassertion
- Timing utilities
- Data conversion utilities

## Key Features

### Logging System
- Configurable logging with fallback mechanisms
- Support for both file and console output
- Automatic log directory creation

### Clock Management
- Start clocks with configurable frequencies
- Wait for clock cycles (rising or falling edges)

### Data Conversion
- Convert between various numerical formats (hex, binary, integer)
- Convert between bytearrays and hex strings
- Format decimals with leading zeros

## Important Methods

### Initialization
```python
def __init__(self, dut):
    """Initializes the testbench object with the DUT and sets up logging."""
```
Initializes the testbench with the Device Under Test (DUT). Sets up logging based on environment variables or defaults.

### Clock Control
```python
async def start_clock(self, clk_name, freq=10, units='ns'):
    """Starts a clock signal for the specified DUT."""
```
Starts a clock signal with the specified name, frequency, and time units.

```python
async def wait_clocks(self, clk_name, count=1, delay=100, units='ps'):
    """Waits for a specified number of rising edges on the clock signal."""
```
Waits for a specified number of rising edges on the clock.

```python
async def wait_falling_clocks(self, clk_name, count=1, delay=100, units='ps'):
    """Waits for a specified number of falling edges on the clock signal."""
```
Waits for a specified number of falling edges on the clock.

### Reset Control
```python
def assert_reset(self):
    """Base method to assert reset"""
```
Template method for asserting reset - should be overridden in derived classes.

```python
def deassert_reset(self):
    """Base method to deassert reset"""
```
Template method for deasserting reset - should be overridden in derived classes.

### Utility Methods
```python
@staticmethod
def convert_param_type(value, default):
    """Converts environment variable values to the correct type based on the default value."""
```
Converts parameters based on their default type (bool, int, float).

```python
@staticmethod
def convert_to_int(value):
    """Convert a value to an integer, handling hexadecimal strings."""
```
Converts a value to an integer, handling hex strings like `"8'hXX"`.

```python
@staticmethod
def hex_format(value, max_value):
    """Format an integer value as a hexadecimal string with leading zeros."""
```
Formats an integer as a hex string with appropriate width based on max value.

```python
@staticmethod
def bytearray_to_hex(bytearray_value):
    """Convert a single bytearray to a hex string."""
```
Converts a bytearray to a hex string representation.

```python
@staticmethod
def format_dec(decimal, width):
    """Format a decimal to a string prepending 0's"""
```
Formats a decimal with leading zeros to specified width.

## Usage Example

```python
class MyTestbench(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        # Custom initialization
        
    async def run_test(self):
        # Start clock
        await self.start_clock("clk", freq=100, units='MHz')
        
        # Assert reset
        self.assert_reset()
        await self.wait_clocks("clk", 10)
        
        # Deassert reset
        self.deassert_reset()
        
        # Test logic here
        
        self.log.info("Test completed successfully")
```

## Important Notes
- The class automatically handles log file creation and directory setup
- Default log level is DEBUG
- Clock frequencies are specified with a value and units (e.g., 10, 'ns')
- Override `assert_reset` and `deassert_reset` for device-specific reset behavior
