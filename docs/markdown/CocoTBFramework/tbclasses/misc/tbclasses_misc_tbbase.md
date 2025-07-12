# tbbase.py

Base testbench class providing common infrastructure and standardized patterns for all testbenches in the CocoTBFramework. This module establishes the foundation for consistent testbench development with built-in logging, configuration management, and component lifecycle handling.

## Overview

The `tbbase.py` module provides the `TBBase` class that serves as the foundation for all testbenches in the framework. It standardizes common operations, provides consistent logging, manages component lifecycles, and establishes patterns for testbench configuration and execution.

### Key Features
- **Standardized initialization** and setup patterns
- **Built-in logging framework** with configurable levels
- **Component lifecycle management** for proper startup/shutdown
- **Configuration management** with parameter validation
- **Clock and reset handling** with configurable timing
- **Test execution framework** with phase management
- **Error handling and recovery** mechanisms
- **Resource management** and cleanup

## Core Classes

### TBBase

Base class for all testbenches providing common infrastructure and standardized patterns.

#### Constructor

```python
TBBase(dut, test_name="TBBase", clock_period=10, reset_cycles=5, 
       log_level="INFO", enable_waves=True, **kwargs)
```

**Parameters:**
- `dut`: Device Under Test entity
- `test_name`: Test identifier for logging and reporting (default: "TBBase")
- `clock_period`: Clock period in nanoseconds (default: 10ns = 100MHz)
- `reset_cycles`: Number of clock cycles for reset assertion (default: 5)
- `log_level`: Logging level ("DEBUG", "INFO", "WARNING", "ERROR") (default: "INFO")
- `enable_waves`: Enable waveform generation (default: True)
- `**kwargs`: Additional configuration parameters

```python
# Basic testbench creation
class MyTestbench(TBBase):
    def __init__(self, dut):
        super().__init__(
            dut=dut,
            test_name="MyAdvancedTest",
            clock_period=5,  # 200MHz
            reset_cycles=10,
            log_level="DEBUG"
        )
```

#### Core Properties

- `dut`: Device Under Test reference
- `test_name`: Current test identifier
- `log`: Logger instance for this testbench
- `clock_period`: Clock period in nanoseconds
- `reset_cycles`: Reset assertion duration
- `components`: Dictionary of managed components
- `config`: Configuration dictionary
- `stats`: Test execution statistics
- `phase`: Current test execution phase

## Initialization and Setup

### `initialize()`

Perform testbench initialization including clock setup, reset management, and component registration.

```python
async def initialize(self):
    """Override this method for custom initialization"""
    await super().initialize()
    
    # Your custom initialization
    self.setup_protocol_components()
    self.configure_test_parameters()
    
    self.log.info("Custom testbench initialization complete")
```

**Default Initialization Sequence:**
1. Clock signal detection and configuration
2. Reset signal detection and setup
3. Component registration and validation
4. Configuration parameter validation
5. Statistics initialization
6. Waveform setup (if enabled)

### `setup_clock(clock_signal=None)`

Configure the testbench clock with automatic signal detection.

**Parameters:**
- `clock_signal`: Clock signal reference (auto-detected if None)

```python
# Automatic clock detection
await tb.setup_clock()

# Manual clock specification
await tb.setup_clock(dut.custom_clk)
```

### `setup_reset(reset_signal=None, active_low=True)`

Configure reset signal with configurable polarity and timing.

**Parameters:**
- `reset_signal`: Reset signal reference (auto-detected if None)
- `active_low`: True for active-low reset (default: True)

```python
# Standard active-low reset
await tb.setup_reset()

# Active-high reset
await tb.setup_reset(reset_signal=dut.rst, active_low=False)
```

## Component Management

### `register_component(name, component)`

Register a component for lifecycle management.

**Parameters:**
- `name`: Component identifier
- `component`: Component instance

```python
# Register components for automatic management
tb.register_component("master", gaxi_master)
tb.register_component("slave", gaxi_slave)
tb.register_component("monitor", protocol_monitor)
```

### `get_component(name)`

Retrieve a registered component by name.

**Parameters:**
- `name`: Component identifier

**Returns:** Component instance or None if not found

```python
master = tb.get_component("master")
if master:
    await master.send(packet)
```

### `start_components()`

Start all registered components in proper order.

```python
# Start all components
await tb.start_components()

# Components start in registration order
# Override for custom startup sequence
```

### `stop_components()`

Stop all registered components with proper cleanup.

```python
# Stop all components
await tb.stop_components()

# Cleanup happens in reverse registration order
```

## Test Execution Framework

### `run_test(test_function, *args, **kwargs)`

Execute a test function with proper setup and teardown.

**Parameters:**
- `test_function`: Async function to execute
- `*args`: Arguments to pass to test function
- `**kwargs`: Keyword arguments to pass to test function

```python
async def my_test_sequence(tb, iterations):
    for i in range(iterations):
        await tb.execute_transaction(i)

# Run test with framework management
await tb.run_test(my_test_sequence, 100)
```

### `set_phase(phase_name)`

Set the current test execution phase for tracking and logging.

**Parameters:**
- `phase_name`: Phase identifier string

```python
tb.set_phase("initialization")
# ... initialization code ...

tb.set_phase("main_test")
# ... main test logic ...

tb.set_phase("cleanup")
# ... cleanup code ...
```

### `checkpoint(name, metadata=None)`

Create a test checkpoint for debugging and analysis.

**Parameters:**
- `name`: Checkpoint identifier
- `metadata`: Optional dictionary of checkpoint data

```python
# Simple checkpoint
tb.checkpoint("test_midpoint")

# Checkpoint with metadata
tb.checkpoint("transaction_complete", {
    'transaction_id': 42,
    'latency': 150,
    'status': 'success'
})
```

## Configuration Management

### `set_config(key, value)`

Set a configuration parameter with validation.

**Parameters:**
- `key`: Configuration key
- `value`: Configuration value

```python
tb.set_config("max_transactions", 1000)
tb.set_config("timeout_cycles", 500)
tb.set_config("randomization_seed", 12345)
```

### `get_config(key, default=None)`

Get a configuration parameter value.

**Parameters:**
- `key`: Configuration key
- `default`: Default value if key not found

**Returns:** Configuration value or default

```python
max_trans = tb.get_config("max_transactions", 100)
timeout = tb.get_config("timeout_cycles", 1000)
```

### `validate_config()`

Validate all configuration parameters.

```python
# Override for custom validation
def validate_config(self):
    super().validate_config()
    
    # Custom validation rules
    if self.get_config("max_transactions") <= 0:
        raise ValueError("max_transactions must be positive")
```

## Statistics and Reporting

### `update_stats(key, value=1)`

Update a statistics counter.

**Parameters:**
- `key`: Statistics key
- `value`: Value to add (default: 1)

```python
tb.update_stats("transactions_sent")
tb.update_stats("data_bytes", 64)
tb.update_stats("errors", 1)
```

### `get_stats(key=None)`

Get statistics values.

**Parameters:**
- `key`: Specific statistics key (returns all if None)

**Returns:** Statistics value or complete statistics dictionary

```python
# Get specific statistic
error_count = tb.get_stats("errors")

# Get all statistics
all_stats = tb.get_stats()
```

### `generate_report()`

Generate a comprehensive test report.

**Returns:** Dictionary containing test execution report

```python
report = tb.generate_report()
print(f"Test: {report['test_name']}")
print(f"Duration: {report['execution_time']:.2f}s")
print(f"Transactions: {report['stats']['transactions_sent']}")
```

## Advanced Features

### `wait_for_condition(condition_func, timeout_cycles=1000)`

Wait for a specific condition with timeout.

**Parameters:**
- `condition_func`: Function that returns True when condition is met
- `timeout_cycles`: Maximum cycles to wait (default: 1000)

```python
# Wait for specific signal condition
await tb.wait_for_condition(
    lambda: dut.status.value == 1,
    timeout_cycles=500
)

# Wait for component ready
await tb.wait_for_condition(
    lambda: tb.get_component("master").is_ready(),
    timeout_cycles=100
)
```

### `add_cleanup(cleanup_func)`

Register a cleanup function to be called during teardown.

**Parameters:**
- `cleanup_func`: Function to call during cleanup

```python
def close_files():
    if hasattr(tb, 'output_file'):
        tb.output_file.close()

tb.add_cleanup(close_files)
```

## Usage Patterns

### Basic Testbench Implementation

```python
import cocotb
from cocotb.triggers import Timer, RisingEdge
from CocoTBFramework.tbclasses.misc.tbbase import TBBase

class SimpleTestbench(TBBase):
    def __init__(self, dut):
        super().__init__(
            dut=dut,
            test_name="SimpleTest",
            clock_period=10,
            reset_cycles=5
        )
    
    async def initialize(self):
        await super().initialize()
        # Custom initialization
        self.setup_components()
    
    def setup_components(self):
        # Component setup
        pass

@cocotb.test()
async def simple_test(dut):
    tb = SimpleTestbench(dut)
    await tb.initialize()
    
    # Test implementation
    await tb.run_test(test_sequence)
    
    # Generate final report
    report = tb.generate_report()
    tb.log.info(f"Test completed: {report}")
```

### Advanced Testbench with Monitoring

```python
from CocoTBFramework.tbclasses.misc.tbbase import TBBase
from CocoTBFramework.tbclasses.misc.advanced_monitoring import advanced_monitoring

class AdvancedTestbench(TBBase):
    def __init__(self, dut):
        super().__init__(
            dut=dut,
            test_name="AdvancedTest",
            clock_period=5,
            log_level="DEBUG"
        )
    
    async def run_monitored_test(self, test_name):
        with advanced_monitoring(test_name) as monitor:
            tb.set_phase("initialization")
            await self.initialize()
            monitor.checkpoint("init_complete")
            
            tb.set_phase("main_test")
            await self.execute_main_test()
            monitor.checkpoint("main_complete")
            
            tb.set_phase("verification")
            await self.verify_results()
            monitor.checkpoint("verification_complete")
```

### Configuration-Driven Testbench

```python
class ConfigurableTestbench(TBBase):
    def __init__(self, dut, config_file=None):
        super().__init__(dut, test_name="ConfigurableTest")
        
        # Load configuration
        if config_file:
            self.load_config_file(config_file)
        
        # Set default configurations
        self.set_config("transaction_count", 100)
        self.set_config("data_width", 32)
        self.set_config("randomize_delays", True)
    
    def validate_config(self):
        super().validate_config()
        
        # Custom validation
        if self.get_config("data_width") not in [8, 16, 32, 64]:
            raise ValueError("Invalid data_width")
    
    async def execute_configurable_test(self):
        count = self.get_config("transaction_count")
        width = self.get_config("data_width")
        
        for i in range(count):
            data = self.generate_test_data(width)
            await self.send_transaction(data)
            self.update_stats("transactions_sent")
```

## Integration with Other Components

The TBBase class is designed to work seamlessly with other CocoTBFramework components:

- **Protocol Components**: Automatic component lifecycle management
- **Monitor Bus**: Built-in support for monitor bus integration
- **Advanced Monitoring**: Native support for monitoring context
- **Utilities**: Integrated with utilities for path and environment management

## Best Practices

1. **Always call super().initialize()** in custom initialization methods
2. **Use register_component()** for automatic lifecycle management
3. **Implement proper cleanup** using add_cleanup() for resources
4. **Use checkpoints and phases** for structured test execution
5. **Validate configurations** to catch errors early
6. **Use statistics tracking** for test analysis and debugging
7. **Generate comprehensive reports** for test documentation

The TBBase class provides a robust foundation for building scalable, maintainable testbenches that follow consistent patterns and provide comprehensive observability into test execution.