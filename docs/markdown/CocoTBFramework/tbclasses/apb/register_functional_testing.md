# Functional Testing with Register Tuples

This guide explains how to use the `create_sequence_from_tuples` factory function for functional testing of registers in the APB framework.

## Overview

Functional testing often requires setting up specific register configurations to validate DUT behavior. The `create_sequence_from_tuples` factory simplifies this by allowing you to define register configurations as simple tuples and automatically generating the APB sequence needed to implement them.

## Tuple Format

Each tuple follows the format:

```python
(register_name, field_name, value)
```

Where:
- `register_name`: Name of the register as defined in the register map
- `field_name`: Name of the field within that register
- `value`: Value to write to the field (integer)

## Creating Test Sequences

The factory function takes a list of these tuples and generates a sequence:

```python
def create_sequence_from_tuples(reg_map, reg_field_values, name="functional_test", options=None):
    """
    Create an APB sequence from a list of (register, field, value) tuples.
    
    Args:
        reg_map: RegisterMap instance containing register definitions
        reg_field_values: List of (register, field, value) tuples
        name: Name for the sequence
        options: Dictionary of options (delay, verify, etc.)
        
    Returns:
        APBSequence: Configured test sequence
    """
```

### Key Features

1. **Automatic Field Masking**: The function automatically creates the correct bit masks for each field, preserving other fields in the register.

2. **Read-Modify-Write**: For readable registers, the function performs read-modify-write operations to modify only the specified field.

3. **Validation**: The function validates that registers and fields exist and that values fit within field widths.

4. **Verification**: Optional read-back verification ensures written values are correctly stored.

## Creating Preset Configurations

A common approach is to define preset configurations in a global file:

```python
# register_presets.py

# Configuration for device initialization
INIT_CONFIG = [
    ("main_control", "enable", 1),          # Enable the device
    ("main_control", "error_mask", 0x7F),   # Enable all error types
    ("arqos", "descriptor_arqos", 5),       # Set descriptor quality of service
    ("arqos", "data_arqos", 3),             # Set data quality of service
    ("chan_enable", "chan_enable", 0x1),    # Enable channel 0
]

# Configuration for error injection test
ERROR_CONFIG = [
    ("main_control", "error_mask", 0x3),    # Enable specific errors
    ("descr_cntr_prog", "descr_cntr_ena", 1),  # Enable descriptor counter
    ("descr_cntr_prog", "descr_cntr_sel", 7),  # Select counter 7
]

# Configuration for device reset
RESET_CONFIG = [
    ("reset_chan", "reset_chan", 0xFFFFFFFF),  # Reset all channels
    ("main_control", "idle", 1),               # Set idle mode
]
```

## Usage Examples

### Basic Usage

```python
from register_presets import INIT_CONFIG

# Create register map
reg_map = RegisterMap(
    "registers.py",
    apb_data_width=32,
    apb_addr_width=24,
    start_address=0x7F0000,
    log=log
)

# Create and execute initialization sequence
init_sequence = create_sequence_from_tuples(
    reg_map,
    INIT_CONFIG,
    name="initialization"
)

await run_test_sequence(apb_master, init_sequence)
```

### Custom Settings

```python
# Define custom configuration inline
dma_config = [
    ("main_control", "full_packet", 1),       # Enable full packet mode
    ("descr_map", "descr_data", 0x12345678),  # Set descriptor 0 data
    ("arqos", "data_arqos", 7),               # Set high QoS for data
]

# Create sequence with options
dma_sequence = create_sequence_from_tuples(
    reg_map,
    dma_config,
    name="dma_setup",
    options={
        "delay": 5,        # 5 cycle delay between transactions
        "verify": True     # Verify writes with read-back
    }
)

await run_test_sequence(apb_master, dma_sequence)
```

### Sequential Test Steps

```python
# Run multiple configuration steps in sequence
async def test_dma_transfer(dut, reg_map, apb_master):
    # Step 1: Initialize the device
    init_seq = create_sequence_from_tuples(reg_map, INIT_CONFIG)
    await run_test_sequence(apb_master, init_seq)
    
    # Step 2: Configure DMA
    dma_seq = create_sequence_from_tuples(reg_map, dma_config)
    await run_test_sequence(apb_master, dma_seq)
    
    # Step 3: Start transfer
    start_seq = create_sequence_from_tuples(reg_map, [
        ("main_control", "idle", 0)  # Clear idle to start
    ])
    await run_test_sequence(apb_master, start_seq)
    
    # Step 4: Wait for completion
    await cocotb.triggers.Timer(1000, units='ns')
    
    # Step 5: Check status
    status_seq = create_sequence_from_tuples(reg_map, [], name="status_check")
    # Add a read operation to check status register
    status_seq.pwrite_seq.append(False)
    status_seq.addr_seq.append(reg_map.start_address + 0x400)  # Status register
    status_results = await run_test_sequence(apb_master, status_seq)
    
    # Check completion bit
    completion_status = (status_results[0].prdata >> 8) & 0x1
    assert completion_status == 1, "DMA transfer did not complete"
```

## Test Execution

The `run_test_sequence` function handles sequence execution:

```python
async def run_test_sequence(apb_master, sequence, verify_func=None):
    """
    Run a register test sequence through an APB master.
    
    Args:
        apb_master: APB master driver
        sequence: Test sequence to run
        verify_func: Optional function to verify each transaction
        
    Returns:
        List of transaction results
    """
```

This function:
1. Executes each transaction in the sequence
2. Handles read-modify-write operations
3. Tracks read data for subsequent writes
4. Calls an optional verification function
5. Returns the list of transaction results

### Custom Verification

You can provide a verification function for custom checks:

```python
async def verify_transaction(packet, index):
    """Custom verification for each transaction"""
    # For read transactions
    if packet.pwrite == 0:
        # Check specific address
        if packet.paddr == 0x7F0400:  # Status register
            # Verify specific bits
            status = packet.prdata
            if (status & 0x1) != 1:
                log.error(f"Device not ready, status: 0x{status:08X}")
            # Check error bits
            if (status & 0xE0) != 0:
                log.error(f"Error detected, status: 0x{status:08X}")

# Use the verification function
await run_test_sequence(apb_master, sequence, verify_func=verify_transaction)
```

## Managing Complex Tests

For more complex tests, you can organize your register configurations hierarchically:

```python
# Test phases
SETUP_PHASE = [
    # Initial configuration
]

EXECUTION_PHASE = [
    # Running configuration
]

VERIFICATION_PHASE = [
    # Checking configuration
]

CLEANUP_PHASE = [
    # Reset configuration
]

# Test cases
TEST_CASE_1 = SETUP_PHASE + [
    # Test-specific settings
] + EXECUTION_PHASE + VERIFICATION_PHASE + CLEANUP_PHASE

TEST_CASE_2 = SETUP_PHASE + [
    # Different test-specific settings
] + EXECUTION_PHASE + VERIFICATION_PHASE + CLEANUP_PHASE
```

## Best Practices

1. **Group Related Settings**: Keep related register settings together in logical groups.

2. **Add Comments**: Document the purpose of each register/field setting.

3. **Validate Field Width**: Ensure values fit within their field widths to avoid truncation.

4. **Test Incremental Changes**: Build tests step by step, validating register settings at each stage.

5. **Include Verification**: Always read back written values to verify correct operation.

6. **Create Reusable Parts**: Define common configuration segments that can be reused across tests.

7. **Handle Special Registers**: Be aware of special register types like write-only, or write-1-to-clear fields.

8. **Time-Sensitive Operations**: Include appropriate delays between operations that might be time-sensitive.

## Conclusion

The tuple-based approach to register testing offers:

- **Simplicity**: Easy to define and understand register configurations
- **Readability**: Clear mapping between configurations and intended behavior
- **Reusability**: Ability to compose tests from predefined building blocks
- **Automation**: Automatic handling of read-modify-write operations and field masking

This makes it ideal for creating maintainable, self-documenting functional tests that focus on device behavior rather than register access mechanisms.

## Navigation

[↑ APB Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
