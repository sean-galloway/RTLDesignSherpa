# APB Factories Deep Dive

This document provides a detailed analysis of the APB factory functions from `apb_factories.py`. These factory functions simplify the creation and configuration of APB components for hardware verification.

## Design Philosophy

The factory functions follow several key design principles:

1. **Simplicity**: Provide easy-to-use, consistent interfaces for creating components
2. **Configuration**: Enable extensive customization through parameters
3. **Defaults**: Provide sensible defaults that work in common scenarios
4. **Composition**: Support the creation of complex verification environments from simple components

## Factory Function Architecture

Each factory function follows a similar pattern:

```python
def create_component(dut, other_required_params, optional_param1=default1, optional_param2=default2, ...):
    """Documentation string with parameter descriptions."""
    
    # Process parameters and set defaults if needed
    
    # Create the component
    component = ComponentClass(
        dut,
        processed_params,
        ...
    )
    
    # Additional configuration
    
    # Return the component
    return component
```

This architecture:
- Makes required parameters explicit (no defaults)
- Provides defaults for common configuration options
- Documents parameters and return values
- Processes parameters before creating components
- Returns the fully configured component

## Core Factory Functions

### 1. `create_apb_master`

Creates an APB master component with configuration:

```python
def create_apb_master(dut, title, prefix, clock, addr_width=32, data_width=32,
                    randomizer=None, log=None):
    """
    Create an APB Master component with configuration.
    
    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        addr_width: Address width in bits
        data_width: Data width in bits
        randomizer: Timing randomizer
        log: Logger instance (default: dut's logger)
        
    Returns:
        APBMaster instance
    """
    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)
    
    # Create default randomizer if none provided
    if randomizer is None:
        randomizer = FlexRandomizer({
            'psel':    ([[0, 0], [1, 5], [6, 10]], [5, 3, 1]),
            'penable': ([[0, 0], [1, 3]], [3, 1]),
        })
    
    return APBMaster(
        dut,
        title,
        prefix,
        clock,
        bus_width=data_width,
        addr_width=addr_width,
        randomizer=randomizer,
        log=log
    )
```

This function:
1. Processes the logger (using DUT's logger if none provided)
2. Creates a default randomizer with specific delay distributions
3. Creates and returns the APBMaster instance with the processed parameters

### 2. `create_apb_slave`

Creates an APB slave component with configuration:

```python
def create_apb_slave(dut, title, prefix, clock, addr_width=32, data_width=32,
                    registers=None, randomizer=None, log=None,
                    error_overflow=False):
    """
    Create an APB Slave component with configuration.
    
    Args:
        dut: Device under test
        title: Component title
        prefix: Signal prefix
        clock: Clock signal
        addr_width: Address width in bits
        data_width: Data width in bits
        registers: Register values (or number of registers)
        randomizer: Timing randomizer
        log: Logger instance (default: dut's logger)
        error_overflow: Whether to generate errors on address overflow
        
    Returns:
        APBSlave instance
    """
    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)
    
    # Process registers parameter
    if registers is None:
        registers = []
    elif isinstance(registers, int):
        # If registers is an integer, treat it as the number of registers
        registers = [0] * (registers * (data_width // 8))
    
    return APBSlave(
        dut,
        title,
        prefix,
        clock,
        registers=registers,
        bus_width=data_width,
        addr_width=addr_width,
        randomizer=randomizer,
        log=log,
        error_overflow=error_overflow
    )
```

This function adds additional processing:
1. Handles the registers parameter, which can be a list or an integer
2. If registers is an integer, creates a zero-initialized register array

### 3. `create_apb_monitor`

Creates an APB monitor component with configuration:

```python
def create_apb_monitor(dut, title, prefix, clock, addr_width=32, data_width=32, log=None):
    """
    Create an APB Monitor component with configuration.
    
    Args:
        dut: Device under test
        title: Component title
        clock: Clock signal
        addr_width: Address width in bits
        data_width: Data width in bits
        log: Logger instance (default: dut's logger)
        
    Returns:
        APBMonitor instance
    """
    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)
    
    return APBMonitor(
        dut,
        title,
        prefix,
        clock,
        bus_width=data_width,
        addr_width=addr_width,
        log=log
    )
```

The monitor factory is simpler as it doesn't require randomizers or register arrays.

### 4. `create_apb_scoreboard`

Creates an APB scoreboard for verification:

```python
def create_apb_scoreboard(name, addr_width=32, data_width=32, log=None):
    """
    Create an APB Scoreboard with configuration.
    
    Args:
        name: Scoreboard name
        addr_width: Address width in bits
        data_width: Data width in bits
        log: Logger instance
        
    Returns:
        APBScoreboard instance
    """
    return APBScoreboard(name, addr_width, data_width, log)
```

### 5. `create_apb_command_handler`

Creates an APB command handler for command/response interface:

```python
def create_apb_command_handler(dut, memory_model, log=None):
    """
    Create an APB Command Handler for APB slave command/response interface.
    
    Args:
        dut: Device under test
        memory_model: Memory model for storage
        log: Logger instance
        
    Returns:
        APBCommandHandler instance
    """
    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)
    
    return APBCommandHandler(dut, memory_model, log)
```

## Complex Factory Functions

### 1. `create_apb_components`

Creates a complete set of APB components (master, slave, monitor, scoreboard):

```python
def create_apb_components(dut, clock, title_prefix="", addr_width=32, data_width=32,
                        memory_lines=1024, randomizer=None, log=None):
    """
    Create a complete set of APB components (master, slave, monitor, scoreboard).
    
    Args:
        dut: Device under test
        clock: Clock signal
        title_prefix: Prefix for component titles
        addr_width: Address width in bits
        data_width: Data width in bits
        memory_lines: Number of memory lines for shared memory model
        randomizer: Timing randomizer for master
        log: Logger instance
        
    Returns:
        Dictionary containing all created components
    """
    # Use dut's logger if none provided
    log = log or getattr(dut, '_log', None)
    
    # Create shared memory model
    memory_model = MemoryModel(
        num_lines=memory_lines,
        bytes_per_line=data_width // 8,
        log=log
    )
    
    # Create APB master
    master = create_apb_master(
        dut,
        f"{title_prefix}APB Master",
        "s_apb",
        clock,
        addr_width=addr_width,
        data_width=data_width,
        randomizer=randomizer,
        log=log
    )
    
    # Create APB monitor
    monitor = create_apb_monitor(
        dut,
        f"{title_prefix}APB Monitor",
        clock,
        addr_width=addr_width,
        data_width=data_width,
        log=log
    )
    
    # Create APB scoreboard
    scoreboard = create_apb_scoreboard(
        f"{title_prefix}APB_Scoreboard",
        addr_width=addr_width,
        data_width=data_width,
        log=log
    )
    
    # Create APB command handler if DUT supports it
    command_handler = None
    if hasattr(dut, 'o_cmd_valid'):
        command_handler = create_apb_command_handler(dut, memory_model, log)
    
    # Return all components
    return {
        'master': master,
        'monitor': monitor,
        'scoreboard': scoreboard,
        'command_handler': command_handler,
        'memory_model': memory_model
    }
```

This function:
1. Creates a shared memory model for all components
2. Creates master, monitor, and scoreboard using their respective factories
3. Optionally creates a command handler if the DUT supports it
4. Returns a dictionary with all created components

### 2. `create_apb_sequence`

Creates an APB sequence with predefined patterns:

```python
def create_apb_sequence(name="basic", num_regs=10, base_addr=0,
                        pattern="alternating", data_width=32,
                        randomize_delays=True):
    """
    Create an APB Sequence for testing.
    
    Args:
        name: Sequence name
        num_regs: Number of registers to test
        base_addr: Base address
        pattern: Pattern type ("alternating", "burst", "strobe", "stress")
        data_width: Data width in bits
        randomize_delays: Whether to include random delays
        
    Returns:
        APBSequence instance
    """
    # Implementation of sequence creation for different patterns
    if pattern == "alternating":
        # Create alternating write-read pattern
        # ...
    elif pattern == "burst":
        # Create burst pattern (all writes followed by all reads)
        # ...
    elif pattern == "strobe":
        # Create strobe test pattern
        # ...
    elif pattern == "stress":
        # Create randomized stress test pattern
        # ...
    else:
        raise ValueError(f"Unknown pattern type: {pattern}")
```

This function:
1. Takes a pattern type parameter that determines the test strategy
2. Creates sequences with different write/read patterns, addresses, and timing
3. For complex patterns like "stress", uses randomization for additional variability

## Implementation Details

### 1. Parameter Processing

The factories handle parameters intelligently:

```python
# Logger handling
log = log or getattr(dut, '_log', None)

# Registers as int or list
if registers is None:
    registers = []
elif isinstance(registers, int):
    registers = [0] * (registers * (data_width // 8))
```

### 2. Default Randomizers

Default randomizers define realistic timing distributions:

```python
randomizer = FlexRandomizer({
    'psel':    ([[0, 0], [1, 5], [6, 10]], [5, 3, 1]),
    'penable': ([[0, 0], [1, 3]], [3, 1]),
})
```

This creates a distribution where:
- PSEL has 5/9 chance of 0 delay, 3/9 chance of 1-5 cycles, 1/9 chance of 6-10 cycles
- PENABLE has 3/4 chance of 0 delay, 1/4 chance of 1-3 cycles

### 3. Test Patterns

The sequence factory supports several test patterns:

- **alternating**: Alternating write and read operations to verify basic functionality
- **burst**: All writes followed by all reads to test throughput
- **strobe**: Various strobe patterns to test byte enable functionality
- **stress**: Random mix of operations to stress test the system

### 4. Dynamic Component Detection

Some factories can adapt to the DUT's capabilities:

```python
# Create APB command handler if DUT supports it
command_handler = None
if hasattr(dut, 'o_cmd_valid'):
    command_handler = create_apb_command_handler(dut, memory_model, log)
```

This allows the factory to work with different DUT architectures without modification.

## Factory Design Patterns

The factories use several design patterns:

1. **Builder Pattern**: Create complex objects step by step
2. **Factory Method**: Create objects without specifying exact class
3. **Composition**: Build complex objects from simpler ones
4. **Sensible Defaults**: Provide defaults for common cases
5. **Dependency Injection**: Pass dependencies like loggers and memory models

## Advanced Features

### 1. APB-GAXI Transformation

The `create_apb_transformer` function creates a transformer between APB and GAXI protocols:

```python
def create_apb_transformer(gaxi_field_config, gaxi_packet_class, log=None):
    """
    Create a transformer from APB to GAXI protocol.
    
    Args:
        gaxi_field_config: GAXI field configuration
        gaxi_packet_class: GAXI packet class
        log: Logger instance
        
    Returns:
        APBtoGAXITransformer instance
    """
    return APBtoGAXITransformer(gaxi_field_config, gaxi_packet_class, log)
```

### 2. APB Packet Creation

The `create_apb_packet` function creates an APB packet with specific field values:

```python
def create_apb_packet(count=0, pwrite=0, paddr=0, pwdata=0, prdata=0, 
                    pstrb=0, pprot=0, pslverr=0, addr_width=32, data_width=32):
    """
    Create an APB packet with the given field values.
    """
    return APBPacket(
        count=count,
        pwrite=pwrite,
        paddr=paddr,
        pwdata=pwdata,
        prdata=prdata,
        pstrb=pstrb,
        pprot=pprot,
        pslverr=pslverr,
        addr_width=addr_width,
        data_width=data_width
    )
```

## Implementation Insights

1. **Consistency**: All factories follow similar parameter patterns
2. **Composability**: Each factory returns components that can be used together
3. **Flexibility**: Parameters allow customization for different verification needs
4. **Reuse**: Factories call other factories to avoid code duplication
5. **Smart defaults**: Default values work for common verification scenarios
6. **Extensibility**: The pattern can be extended for new components/features
