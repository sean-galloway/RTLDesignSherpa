# APB Test Classes Overview

## Introduction

The APB (AMBA Peripheral Bus) Test Classes provide a comprehensive framework for verifying APB-based register interfaces in hardware designs. These classes focus on register map handling, command processing, and systematic register testing methodologies.

APB is a simple, low-bandwidth address/data protocol suitable for peripheral devices. It's characterized by a simple phased approach with setup and access phases, basic handshaking, and typically lower bandwidth compared to AXI or other advanced protocols.

## Core Components and Workflow

The APB Test Classes are organized around several key components that work together to create a comprehensive register verification environment:

1. **Register Map**: Manages register definitions, state, and access patterns
2. **Command Handler**: Processes APB commands and responses
3. **Functional Testing**: Provides simplified register test methodologies
4. **Test Factory**: Generates comprehensive register test scenarios
5. **Register Structure**: Documents and validates register definitions

Typical workflow:
1. Load register definitions from a UVM file
2. Create register tests using factory functions or tuple-based configuration
3. Execute tests through an APB master component
4. Process results and verify register behavior

## APB Command Handler

The APB Command Handler serves as the "processor" behind an APB slave's command/response interface. It enables verification of APB slaves by:

- Monitoring commands from the APB slave
- Processing these commands using a memory model
- Driving responses back to the APB slave

The handler implements a complete command processing loop:
1. Command detection (waiting for valid signal)
2. Command processing (read/write operations)
3. Command acknowledgment
4. Response generation
5. Response handshake

The APB Command Handler is particularly useful when:
- Testing standalone APB slaves
- Verifying command/response interfaces
- Implementing custom APB slave behavior

## Register Map

The Register Map class serves as a bridge between abstract register definitions from UVM files and concrete APB transactions. Key capabilities include:

- Loading register definitions from UVM Python files
- Tracking register state
- Generating APB transactions for register access
- Validating register operations

The Register Map works at the field level, not just the register level, supporting:
- Field-oriented register access
- Multiple register types (scalar, arrays)
- Multi-word registers
- Read-modify-write operations

## Register Testing

### Tuple-Based Functional Testing

The tuple-based approach simplifies register testing by allowing users to define register configurations as simple tuples:

```python
config = [
    ("register_name", "field_name", value),
    # Additional register settings...
]
```

This approach offers:
- **Simplicity**: Easy to define and understand
- **Readability**: Clear mapping between configuration and behavior
- **Reusability**: Ability to compose tests from predefined blocks
- **Automation**: Automatic field masking and read-modify-write operations

### Register Test Factory

The Register Test Factory provides factory functions for generating different types of register tests:

1. **Walking Ones/Zeros**: Tests register access with walking bit patterns
2. **Field-Specific**: Targets individual fields with specific test values
3. **Access Rights**: Verifies read/write permissions
4. **Reset**: Confirms registers return to default values after reset
5. **Stress**: Performs rapid back-to-back register accesses
6. **Random**: Generates randomized register operations

Each test type is configurable through options, allowing fine-tuned verification based on specific requirements.

## Integration Examples

### Basic Register Walking Test

```python
# Create register map
reg_map = RegisterMap(
    filename="registers.py",
    apb_data_width=32,
    apb_addr_width=24,
    start_address=0x7F0000,
    log=log
)

# Create walking ones test
sequence = create_register_test_sequence(
    reg_map,
    test_type="walk",
    options={
        "pattern": "walking_ones",
        "delay": 2
    }
)

# Run test
await run_test_sequence(apb_master, sequence)
```

### Functional Testing with Tuples

```python
# Define register configuration
init_config = [
    ("main_control", "enable", 1),
    ("main_control", "error_mask", 0x7F),
    ("arqos", "descriptor_arqos", 5),
    ("chan_enable", "chan_enable", 0x1)
]

# Create and execute sequence
init_sequence = create_sequence_from_tuples(
    reg_map,
    init_config,
    name="initialization"
)

await run_test_sequence(apb_master, init_sequence)
```

### APB Command Handler Usage

```python
# Create memory model for storage
memory_model = MemoryModel(
    size=4096,
    bytes_per_line=4,
    log=dut._log
)

# Create and start command handler
cmd_handler = APBCommandHandler(dut, memory_model, log=dut._log)
await cmd_handler.start()

# Configure stimulus for the APB interface
# ...

# Stop command handler after test
await cmd_handler.stop()
```

## Best Practices

1. **Register Definition Structure**: Maintain well-organized register definition files
2. **Test Organization**: Group related register settings together in logical configurations
3. **Field Documentation**: Include comments explaining the purpose of each register/field setting
4. **Incremental Testing**: Build tests step by step, validating register settings at each stage
5. **Verification Coverage**: Use different test types to ensure comprehensive register verification
6. **Reusable Components**: Create common configuration segments that can be reused across tests

## Advanced Topics

### Register Map Structure

The register map structure supports a hierarchical organization:
- Top-level block definitions
- Register definitions
- Field definitions
- Configuration properties

Key characteristics:
- Text-based values (strings for numeric values)
- Hierarchical structure (blocks → registers → fields)
- Access controls at field level
- Detailed addressing information

### Special Register Types

The APB test classes support various register types:
- Standard read/write registers
- Read-only registers
- Write-only registers
- Write-1-to-clear fields
- Write-1-to-set fields
- Register arrays

Each type requires specific handling during test generation and execution.

### Reset Testing

Reset testing verifies that registers return to default values after reset:
1. Read initial register values
2. Write non-default values
3. Apply reset
4. Verify registers return to defaults

This approach ensures correct reset behavior across the design.

## Implementation Notes

- The modules handle both scalar registers and register arrays
- Appropriate bit masking is automatically applied for field-level access
- Verification includes read-back checks to confirm write operations
- Support for different verification methodologies (walking, field, reset, etc.)
- Integration with memory models for data storage and retrieval

## See Also

- [APB Components](../../components/apb/index.md) - APB verification components
- [APB Scoreboard](../../scoreboards/apb_scoreboard.md) - Transaction verification for APB
- [WaveDrom APB](../wavedrom_user/apb.md) - WaveDrom visualization for APB

## Navigation

[↑ APB Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
