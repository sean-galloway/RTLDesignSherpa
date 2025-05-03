# APB Factories Deep Dive

This document provides a detailed analysis of the APB factory functions from the enhanced `apb_factories.py`. These factory functions simplify the creation and configuration of APB components for hardware verification.

## Design Philosophy

The factory functions follow several key design principles:

1. **Simplicity**: Provide easy-to-use, consistent interfaces for creating components
2. **Configuration**: Enable extensive customization through parameters
3. **Defaults**: Provide sensible defaults that work in common scenarios
4. **Composition**: Support the creation of complex verification environments from simple components
5. **Reusability**: Promote code reuse through flexible abstractions

## Factory Function Types

The factory functions can be divided into several categories:

### 1. Component Factories
Functions that create individual APB components:
- `create_apb_master`
- `create_apb_slave`
- `create_apb_monitor`
- `create_apb_scoreboard`
- `create_apb_command_handler`

### 2. Environment Factories
Functions that create complete verification environments:
- `create_apb_components`

### 3. Utility Factories
Functions that create utility objects:
- `create_apb_transformer`
- `create_apb_packet`

### 4. Test Sequence Factories
Functions that create test sequences:
- `create_apb_sequence`
- `create_register_test_sequence`
- `create_sequence_from_tuples`

## Core Component Factories

These functions create the primary APB components:

```python
def create_apb_master(dut, title, prefix, clock, addr_width=32, data_width=32,
                    randomizer=None, log=None):
    """Create an APB Master component with configuration."""
    
def create_apb_slave(dut, title, prefix, clock, addr_width=32, data_width=32,
                   registers=None, randomizer=None, log=None, error_overflow=False):
    """Create an APB Slave component with configuration."""
    
def create_apb_monitor(dut, title, prefix, clock, addr_width=32, data_width=32, log=None):
    """Create an APB Monitor component with configuration."""
    
def create_apb_scoreboard(name, addr_width=32, data_width=32, log=None):
    """Create an APB Scoreboard with configuration."""
    
def create_apb_command_handler(dut, memory_model, log=None):
    """Create an APB Command Handler for APB slave command/response interface."""
```

These functions handle the details of component instantiation and configuration, providing consistent interfaces and sensible defaults.

## Environment Factory

The `create_apb_components` function creates a complete APB verification environment:

```python
def create_apb_components(dut, clock, title_prefix="", addr_width=32, data_width=32,
                        memory_lines=1024, randomizer=None, log=None):
    """Create a complete set of APB components (master, slave, monitor, scoreboard)."""
```

This function:
1. Creates a shared memory model
2. Creates an APB master, monitor, and scoreboard
3. Optionally creates a command handler if supported by the DUT
4. Returns a dictionary containing all components

This simplifies the setup process for common verification scenarios.

## Test Sequence Factory

The `create_apb_sequence` function creates predefined test sequences:

```python
def create_apb_sequence(name="basic", num_regs=10, base_addr=0,
                        pattern="alternating", data_width=32,
                        randomize_delays=True):
    """Create an APB Sequence for testing."""
```

This function supports several test patterns:
- **alternating**: Alternating write-read operations
- **burst**: All writes followed by all reads
- **strobe**: Test different strobe (byte enable) patterns
- **stress**: Random mix of operations with high transaction density

## Enhanced Register Test Factories

The enhanced factories include a powerful register testing framework:

```python
def create_register_test_sequence(reg_map, test_type="walk", options=None):
    """Create a test sequence for register testing based on register map information."""
```

This function provides six test types:
1. **walk**: Walking ones/zeros test for each register
2. **field**: Field-specific testing with preserving other fields
3. **access**: Testing register access rights (R/W, RO, WO, etc.)
4. **reset**: Verifying registers return to default values after reset
5. **stress**: Rapid back-to-back register accesses to test timing
6. **random**: Randomized tests for comprehensive coverage

The implementation delegates to specialized private functions for each test type:
- `_create_walk_test`
- `_create_field_test`
- `_create_access_test`
- `_create_reset_test`
- `_create_stress_test`
- `_create_random_test`

## Functional Register Test Factory

A key addition is the `create_sequence_from_tuples` factory function:

```python
def create_sequence_from_tuples(reg_map, reg_field_values, name="functional_test", options=None):
    """Create an APB sequence from a list of (register, field, value) tuples."""
```

This function:
1. Takes a list of (register, field, value) tuples
2. Validates register and field existence and accessibility
3. Handles field masking and read-modify-write operations
4. Creates a sequence that configures the registers accordingly
5. Optionally includes verification steps

This enables complex functional tests to be defined with simple, readable tuples.

## Test Runner Functions

The factory module includes test runner functions to execute sequences:

```python
async def run_test_sequence(apb_master, sequence, verify_func=None):
    """Run a register test sequence through an APB master."""
```

This function:
1. Executes each transaction in the sequence
2. Handles special data formats like read-modify-write tuples
3. Tracks read data for subsequent operations
4. Supports custom verification callbacks
5. Returns the list of transaction results

## Implementation Details

### Parameter Processing

The factories include standardized parameter handling:

```python
# Use DUT's logger if none provided
log = log or getattr(dut, '_log', None)

# Process registers parameter for slave
if registers is None:
    registers = []
elif isinstance(registers, int):
    registers = [0] * (registers * (data_width // 8))
```

This makes the functions adaptable to different calling patterns.

### Default Randomizers

The factories create default randomizers with realistic timing distributions:

```python
randomizer = FlexRandomizer({
    'psel':    ([[0, 0], [1, 5], [6, 10]], [5, 3, 1]),
    'penable': ([[0, 0], [1, 3]], [3, 1]),
})
```

This creates a distribution where:
- PSEL has 5/9 chance of 0 delay, 3/9 chance of 1-5 cycles, 1/9 chance of 6-10 cycles
- PENABLE has 3/4 chance of 0 delay, 1/4 chance of 1-3 cycles

### Read-Modify-Write Handling

The `create_sequence_from_tuples` function uses tuples for read-modify-write operations:

```python
# If readable, use read-modify-write tuple
if "r" in sw_access:
    # (~field_mask & 0xFFFFFFFF, field_value) means:
    # "Clear these bits (field_mask) and set these bits (field_value)"
    sequence.data_seq.append((~field_mask & 0xFFFFFFFF, field_value))
```

These tuples are then processed by the `run_test_sequence` function:

```python
# Handle read-modify-write tuple
if isinstance(data, tuple) and len(data) == 2:
    mask, value = data
    if addr in read_data:
        # Apply mask and value to previous read data
        data = (read_data[addr] & mask) | value
```

This preserves fields that are not being modified while changing only the targeted field.

### Field Access and Masking

The register test factories include complex field handling:

```python
# Get field offset (position)
offset = field_info.get("offset", "0")
if ":" in offset:
    high, low = map(int, offset.split(":"))
    field_width = high - low + 1
    shift = low
else:
    field_width = 1
    shift = int(offset)
    
# Create field mask
field_mask = ((1 << field_width) - 1) << shift
```

This enables precise targeting of individual fields within registers.

## Factory Design Patterns

The factories use several design patterns:

1. **Factory Method**: Create objects without specifying exact class
2. **Builder Pattern**: Create complex objects step by step
3. **Composition**: Build complex objects from simpler ones
4. **Strategy Pattern**: Different test types use different algorithms
5. **Dependency Injection**: Pass dependencies like loggers and memory models

## Usage Scenarios

### Basic Component Setup

```python
# Create APB master
apb_master = create_apb_master(dut, "APB Master", "s_apb", dut.pclk)

# Create APB slave with 256 registers
apb_slave = create_apb_slave(dut, "APB Slave", "s_apb", dut.pclk, registers=256)

# Create monitor and connect to scoreboard
apb_monitor = create_apb_monitor(dut, "APB Monitor", "s_apb", dut.pclk)
apb_scoreboard = create_apb_scoreboard("APB Scoreboard")
apb_monitor.add_callback(apb_scoreboard.add_actual)
```

### Complete Environment Setup

```python
# Create complete APB environment
components = create_apb_components(dut, dut.pclk, "test_")

# Access individual components
master = components['master']
monitor = components['monitor']
memory_model = components['memory_model']
```

### Test Sequence Generation

```python
# Create alternating read/write sequence
sequence = create_apb_sequence(
    name="basic_test",
    num_regs=10,
    base_addr=0x1000,
    pattern="alternating"
)

# Run the sequence
await run_test_sequence(apb_master, sequence)
```

### Register Map Testing

```python
# Create register map
reg_map = RegisterMap("registers.py", 32, 24, 0x7F0000, log)

# Create register walking ones test
sequence = create_register_test_sequence(
    reg_map,
    test_type="walk",
    options={"pattern": "walking_ones"}
)

# Run the test
await run_test_sequence(apb_master, sequence)
```

### Functional Testing with Tuples

```python
# Define register configurations
register_settings = [
    ("main_control", "enable", 1),
    ("main_control", "error_mask", 0x7F),
    ("interrupt", "eol", 0),
    ("chan_enable", "chan_enable", 0x1),
]

# Create sequence from tuples
sequence = create_sequence_from_tuples(
    reg_map,
    register_settings,
    name="initialization_sequence"
)

# Run the sequence
await run_test_sequence(apb_master, sequence)
```

## Conclusion

The APB factory functions provide a powerful, flexible framework for APB verification:

1. **Component Creation**: Easy creation of APB masters, slaves, monitors, etc.
2. **Environment Setup**: One-line setup of complete verification environments
3. **Test Generation**: Predefined and custom test sequence generation
4. **Register Testing**: Comprehensive register verification based on register maps
5. **Functional Testing**: Simple tuple-based functional test definitions

This abstraction layer significantly reduces the complexity and boilerplate code required for APB verification, enabling test developers to focus on test scenarios rather than implementation details.
