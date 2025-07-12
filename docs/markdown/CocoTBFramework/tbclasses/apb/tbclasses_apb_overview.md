# APB Testbench Classes Overview

The APB testbench classes provide high-level testbench functionality for APB protocol verification. These classes operate at the testbench orchestration level, managing command interfaces, configuration generation, and register-based testing patterns.

## Architecture Overview

The APB testbench classes follow a hierarchical approach for comprehensive verification:

```
┌─────────────────────────────────────────────────────────┐
│                   Test Orchestration                   │
│            (Test Sequences, Verification)              │
└─────────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────────┐
│                APB Testbench Classes                   │
│   ┌─────────────┐ ┌─────────────┐ ┌─────────────┐     │
│   │   Command   │ │ Config Mgmt │ │ Register    │     │
│   │   Handler   │ │   Factory   │ │ Map Testing │     │
│   └─────────────┘ └─────────────┘ └─────────────┘     │
└─────────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────────┐
│                  APB Protocol Layer                    │
│         (Masters, Slaves, Monitors, Packets)          │
└─────────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────────┐
│                   Memory & Config                      │
│      (Memory Model, Field Config, Randomization)      │
└─────────────────────────────────────────────────────────┘
```

## Component Categories

### 🎛️ **Command Interface Management (apb_command_handler.py)**
Handles APB slave command/response interface processing:

- **APBCommandHandler**: Processes commands from APB slave command interface
- **Memory Integration**: Works with memory models for read/write operations
- **Asynchronous Processing**: Independent command processing with proper handshaking

**Key Features:**
- Command interface monitoring and processing
- Memory model integration for data storage/retrieval
- Configurable processing delays and error injection
- Proper APB handshaking protocol implementation
- Background task management for continuous operation

**Use Cases:**
- Testing APB slaves with command/response interfaces
- Creating processor-like behavior behind APB interfaces
- Memory-mapped peripheral simulation
- Command queue processing and response generation

### ⚙️ **Configuration Management (apbgaxiconfig.py)**
Provides configurable APB-GAXI interface configurations:

- **APBGAXIConfig**: Factory for creating field configurations
- **Parameterized Generation**: Configurable address/data widths
- **Field Configuration**: Integration with FieldConfig framework

**Key Features:**
- Configurable bus widths (address, data, strobe)
- Command and response interface field generation
- FieldConfig integration for systematic field management
- Parameterized configuration for different design variants
- Standard field definitions with customizable parameters

**Use Cases:**
- APB-GAXI bridge verification
- Multi-width interface testing
- Configuration-driven testbench setup
- Field-level transaction verification

### 📋 **Register Map Testing (register_map.py)**
Systematic register verification and transaction generation:

- **RegisterMap**: Loads and processes register definitions
- **Transaction Generation**: Creates APB transactions for register testing
- **Field-Level Testing**: Supports bit-level register field verification

**Key Features:**
- Register definition loading from Python files
- Automatic transaction generation for register testing
- Field-level read/write capability analysis
- Even/odd bit pattern testing for comprehensive coverage
- Register state tracking and comparison

**Use Cases:**
- Register map verification
- Peripheral register testing
- Configuration register validation
- Memory-mapped interface verification

## Design Principles

### 1. **High-Level Abstraction**
- Operates above the protocol level for system-wide functionality
- Provides testbench orchestration rather than signal-level control
- Integrates with lower-level components for complete verification

### 2. **Configuration-Driven**
- Parameterized configurations support multiple design variants
- Field-based configuration enables systematic verification
- Register definitions drive automatic test generation

### 3. **Memory Integration**
- Seamless integration with memory models
- Support for realistic memory behavior
- Automatic data management and validation

### 4. **Asynchronous Operation**
- Background processing for continuous operation
- Proper task management and lifecycle control
- Non-blocking operation with other testbench components

## Usage Patterns

### Command Handler Integration

```python
@cocotb.test()
async def apb_command_test(dut):
    # Create memory model
    memory_model = MemoryModel(num_lines=1024, bytes_per_line=4)
    
    # Create command handler
    cmd_handler = APBCommandHandler(
        dut=dut,
        memory_model=memory_model,
        log=logger
    )
    
    # Start background processing
    await cmd_handler.start()
    
    # Test will run with automatic command processing
    # Commands from APB slave are automatically handled
    
    # Clean up
    await cmd_handler.stop()
```

### Configuration-Driven Setup

```python
# Create configuration for specific design
config = APBGAXIConfig(
    addr_width=32,
    data_width=64,
    strb_width=8
)

# Generate field configurations
cmd_field_config = config.create_cmd_field_config()
rsp_field_config = config.create_rsp_field_config()

# Use configurations in component creation
master = GAXIMaster(dut, "Master", "", dut.clk, cmd_field_config)
slave = GAXISlave(dut, "Slave", "", dut.clk, rsp_field_config)
```

### Register Map Verification

```python
# Load register definitions
reg_map = RegisterMap(
    filename="peripheral_registers.py",
    apb_data_width=32,
    apb_addr_width=16,
    start_address=0x40000000,
    log=logger
)

# Generate comprehensive register tests
read_tests = reg_map.generate_read_transactions()
write_even_tests = reg_map.generate_write_even_transactions()
write_odd_tests = reg_map.generate_write_odd_transactions()

# Execute tests using APB master
for transaction in read_tests:
    await apb_master.send(transaction)

# Compare results
expected = read_tests
actual = monitor.captured_transactions
miscompares = reg_map.compare_transactions(expected, actual, "Read Test")
```

### Complete System Integration

```python
@cocotb.test()
async def complete_apb_system_test(dut):
    # 1. Setup configuration
    config = APBGAXIConfig(addr_width=32, data_width=32)
    
    # 2. Create memory model
    memory_model = MemoryModel(num_lines=4096, bytes_per_line=4)
    
    # 3. Setup command handler
    cmd_handler = APBCommandHandler(dut, memory_model, logger)
    await cmd_handler.start()
    
    # 4. Load register map
    reg_map = RegisterMap(
        filename="dut_registers.py",
        apb_data_width=32,
        apb_addr_width=32,
        start_address=0x80000000,
        log=logger
    )
    
    # 5. Execute comprehensive register testing
    test_sequences = [
        reg_map.generate_read_transactions(),
        reg_map.generate_write_even_transactions(),
        reg_map.generate_write_odd_transactions()
    ]
    
    for sequence_name, transactions in zip(
        ["Read", "Write Even", "Write Odd"], 
        test_sequences
    ):
        logger.info(f"Starting {sequence_name} test sequence")
        
        for transaction in transactions:
            await apb_master.send(transaction)
        
        logger.info(f"Completed {sequence_name} test sequence")
    
    # 6. Final verification and cleanup
    await cmd_handler.stop()
    final_report = reg_map.generate_final_report()
    logger.info(f"Test completion report: {final_report}")
```

## Integration Points

### Memory Model Integration
- **Command Handler** uses memory models for read/write processing
- **Register Map** can validate against memory model state
- **Configuration** determines memory access patterns and widths

### Field Configuration Framework
- **APBGAXIConfig** generates FieldConfig objects for components
- **Register Map** can use field configurations for transaction validation
- **Standard field definitions** ensure consistency across components

### Protocol Component Integration
- **Command Handler** works with APB slave components
- **Configuration** supports both APB and GAXI component creation
- **Register Map** generates transactions compatible with APB components

### Test Framework Integration
- **Asynchronous operation** integrates with CocoTB test framework
- **Logging integration** provides comprehensive test visibility
- **Error reporting** integrates with standard verification flows

## Best Practices

### 1. **Lifecycle Management**
```python
# Always start/stop command handlers properly
await cmd_handler.start()
try:
    # Test execution
    pass
finally:
    await cmd_handler.stop()
```

### 2. **Configuration Consistency**
```python
# Use same configuration for related components
config = APBGAXIConfig(addr_width=32, data_width=32)
master_config = config.create_cmd_field_config()
slave_config = config.create_rsp_field_config()

# Components use consistent field definitions
```

### 3. **Register Map Validation**
```python
# Always validate register map loading
try:
    reg_map = RegisterMap(filename, ...)
    logger.info(f"Loaded {len(reg_map.registers)} registers")
except Exception as e:
    logger.error(f"Failed to load register map: {e}")
    raise
```

### 4. **Memory Model Sizing**
```python
# Size memory models appropriately for address space
max_addr = reg_map.get_max_address()
required_lines = (max_addr // bytes_per_line) + 1
memory_model = MemoryModel(num_lines=required_lines, bytes_per_line=4)
```

The APB testbench classes provide the high-level orchestration needed for comprehensive APB verification, bridging between test scenarios and protocol-level components while maintaining the flexibility needed for diverse verification environments.