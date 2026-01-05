<!-- RTL Design Sherpa Documentation Header -->
<table>
<tr>
<td width="80">
  <a href="https://github.com/sean-galloway/RTLDesignSherpa">
    <img src="https://raw.githubusercontent.com/sean-galloway/RTLDesignSherpa/main/docs/logos/Logo_200px.png" alt="RTL Design Sherpa" width="70">
  </a>
</td>
<td>
  <strong>RTL Design Sherpa</strong> · <em>Learning Hardware Design Through Practice</em><br>
  <sub>
    <a href="https://github.com/sean-galloway/RTLDesignSherpa">GitHub</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/docs/DOCUMENTATION_INDEX.md">Documentation Index</a> ·
    <a href="https://github.com/sean-galloway/RTLDesignSherpa/blob/main/LICENSE">MIT License</a>
  </sub>
</td>
</tr>
</table>

---

<!-- End Header -->

# apb_command_handler.py Usage Guide

APB Command Handler for APB slave command/response interface processing. This module provides a command handler that monitors APB slave command interfaces, processes commands using memory models, and drives response interfaces with results.

## Why Use APB Command Handler

The `apb_command_handler.py` module is essential for testing APB slaves with command/response interfaces because it provides:

- **Independent command processing** that operates separately from the APB bus protocol
- **Memory model integration** for realistic read/write behavior with proper data storage
- **Asynchronous operation** that doesn't block other testbench components
- **Configurable processing delays** to simulate realistic processor-like behavior
- **Proper handshaking protocol** implementation for command/response interfaces

## Core Class

### APBCommandHandler

**Purpose**: Acts as the "processor" behind an APB slave's command/response interface, allowing the slave to operate independently of the APB bus.

**When to Use**:
- Testing APB slaves that have separate command/response interfaces
- Creating processor-like behavior behind APB interfaces
- Simulating memory-mapped peripheral processing
- Command queue processing with realistic delays

## Class Architecture

### Command/Response Flow

```
APB Slave DUT              Command Handler              Memory Model
     │                           │                          │
     ├─ o_cmd_valid ────────────►│                          │
     ├─ o_cmd_pwrite ───────────►│                          │
     ├─ o_cmd_paddr ────────────►│                          │
     ├─ o_cmd_pwdata ───────────►│                          │
     ├─ o_cmd_pstrb ────────────►│                          │
     │                           │                          │
     │◄──────────── i_cmd_ready ─┤                          │
     │                           │                          │
     │                           ├─ write/read ────────────►│
     │                           │◄─────────── data ────────┤
     │                           │                          │
     │◄────────── i_rsp_valid ───┤                          │
     │◄────────── i_rsp_prdata ──┤                          │
     │◄────────── i_rsp_pslverr ─┤                          │
     ├─ o_rsp_ready ────────────►│                          │
```

### Constructor

```python
APBCommandHandler(dut, memory_model, log=None)
```

**Parameters:**
- `dut`: Device under test with command/response interface signals
- `memory_model`: MemoryModel instance for data storage and retrieval
- `log`: Logger instance (defaults to dut's logger if available)

**Basic Creation**:
```python
from CocoTBFramework.tbclasses.apb.apb_command_handler import APBCommandHandler
from CocoTBFramework.components.shared.memory_model import MemoryModel

# Create memory model
memory_model = MemoryModel(
    num_lines=1024,     # 1024 memory lines
    bytes_per_line=4,   # 4 bytes per line (32-bit words)
    log=logger
)

# Create command handler
cmd_handler = APBCommandHandler(
    dut=dut,
    memory_model=memory_model,
    log=logger
)
```

## Lifecycle Management

### Starting the Handler

```python
async def start()
```

**Purpose**: Start the background command processing task.

**Usage**:
```python
# Start command processing
await cmd_handler.start()

# Command handler now monitors command interface in background
# and automatically processes commands as they arrive
```

### Stopping the Handler

```python
async def stop()
```

**Purpose**: Stop the background command processing task.

**Usage**:
```python
# Stop command processing (usually in test cleanup)
await cmd_handler.stop()
```

### Reset Handler State

```python
async def reset()
```

**Purpose**: Reset the command handler to initial state.

**Usage**:
```python
# Reset handler state during test
await cmd_handler.reset()
```

## Signal Interface

### Command Interface Signals (Inputs from DUT)

The handler expects these signals from the APB slave DUT:

- `dut.o_cmd_valid` - Command valid signal
- `dut.o_cmd_pwrite` - Write enable (1=write, 0=read)
- `dut.o_cmd_paddr` - Address for the command
- `dut.o_cmd_pwdata` - Write data (for write commands)
- `dut.o_cmd_pstrb` - Write strobes (optional, defaults to 0xFF)

### Response Interface Signals (Outputs to DUT)

The handler drives these signals to the APB slave DUT:

- `dut.i_cmd_ready` - Command ready acknowledgment
- `dut.i_rsp_valid` - Response valid signal
- `dut.i_rsp_prdata` - Read data (for read responses)
- `dut.i_rsp_pslverr` - Slave error indication

### Clock Signal

- `dut.pclk` - Clock for synchronization

## Command Processing Behavior

### Write Command Processing

1. **Command Detection**: Handler waits for `o_cmd_valid` to be asserted
2. **Command Capture**: Captures write address, data, and strobes
3. **Memory Operation**: Converts data to bytearray and writes to memory model
4. **Acknowledgment**: Asserts `i_cmd_ready` for one cycle
5. **Processing Delay**: Configurable delay cycles (default: 2 cycles)
6. **Response**: Asserts `i_rsp_valid` with no data for write operations
7. **Completion**: Waits for `o_rsp_ready` then deasserts `i_rsp_valid`

### Read Command Processing

1. **Command Detection**: Handler waits for `o_cmd_valid` to be asserted
2. **Command Capture**: Captures read address
3. **Memory Operation**: Reads data from memory model and converts to integer
4. **Acknowledgment**: Asserts `i_cmd_ready` for one cycle
5. **Processing Delay**: Configurable delay cycles (default: 2 cycles)
6. **Response**: Asserts `i_rsp_valid` with read data on `i_rsp_prdata`
7. **Completion**: Waits for `o_rsp_ready` then deasserts `i_rsp_valid`

## Usage Patterns

### Basic Command Handler Setup

```python
@cocotb.test()
async def basic_command_handler_test(dut):
    # Create memory model
    memory_model = MemoryModel(
        num_lines=256,      # 256 words of memory
        bytes_per_line=4,   # 32-bit words
        log=logger
    )
    
    # Create command handler
    cmd_handler = APBCommandHandler(
        dut=dut,
        memory_model=memory_model,
        log=logger
    )
    
    # Start command processing
    await cmd_handler.start()
    
    # Your test code here - APB transactions will be automatically
    # processed by the command handler when they reach the slave
    
    # Example: Send APB transactions using master
    # The command handler will automatically process commands
    # from the slave's command interface
    
    # Stop command processing
    await cmd_handler.stop()
```

### Integration with APB Master Testing

```python
@cocotb.test()
async def apb_master_with_command_handler(dut):
    # Setup components
    memory_model = MemoryModel(num_lines=1024, bytes_per_line=4)
    cmd_handler = APBCommandHandler(dut, memory_model, logger)
    
    # Start background processing
    await cmd_handler.start()
    
    # Create APB master for driving transactions
    from CocoTBFramework.components.apb.apb_components import APBMaster
    apb_master = APBMaster(dut, "TestMaster", "apb_", dut.clk)
    
    # Drive APB transactions - command handler processes them automatically
    test_data = [0x12345678, 0xDEADBEEF, 0xCAFEBABE, 0xBAADF00D]
    
    for i, data in enumerate(test_data):
        addr = 0x1000 + (i * 4)
        
        # Write data
        write_packet = APBPacket(pwrite=1, paddr=addr, pwdata=data)
        await apb_master.send(write_packet)
        
        # Read back
        read_packet = APBPacket(pwrite=0, paddr=addr)
        await apb_master.send(read_packet)
    
    # Verify memory contents
    for i, expected_data in enumerate(test_data):
        addr = 0x1000 + (i * 4)
        actual_data = memory_model.bytearray_to_integer(
            memory_model.read(addr, 4)
        )
        assert actual_data == expected_data, f"Mismatch at 0x{addr:X}"
    
    await cmd_handler.stop()
```

### Memory Initialization and Verification

```python
async def test_with_initialized_memory(dut):
    # Create memory model with initial data
    memory_model = MemoryModel(num_lines=512, bytes_per_line=4)
    
    # Initialize memory with known patterns
    for addr in range(0, 0x800, 4):  # Initialize 512 words
        init_data = addr + 0x1000  # Each location contains address + offset
        data_bytes = memory_model.integer_to_bytearray(init_data, 4)
        memory_model.write(addr, data_bytes)
    
    # Create command handler with initialized memory
    cmd_handler = APBCommandHandler(dut, memory_model, logger)
    await cmd_handler.start()
    
    # APB master for testing
    apb_master = APBMaster(dut, "Master", "apb_", dut.clk)
    
    # Read back and verify initial data
    for addr in range(0, 0x800, 16):  # Test every 4th location
        read_packet = APBPacket(pwrite=0, paddr=addr)
        await apb_master.send(read_packet)
        
        # Verify through memory model
        expected = addr + 0x1000
        actual = memory_model.bytearray_to_integer(
            memory_model.read(addr, 4)
        )
        assert actual == expected, f"Address 0x{addr:X}: expected 0x{expected:X}, got 0x{actual:X}"
    
    await cmd_handler.stop()
```

### Error Injection Testing

```python
async def test_command_handler_with_errors(dut):
    # Create memory model
    memory_model = MemoryModel(num_lines=64, bytes_per_line=4)
    cmd_handler = APBCommandHandler(dut, memory_model, logger)
    
    await cmd_handler.start()
    
    # Create APB master
    apb_master = APBMaster(dut, "Master", "apb_", dut.clk)
    
    # Test normal operation
    normal_packet = APBPacket(pwrite=1, paddr=0x100, pwdata=0x12345678)
    await apb_master.send(normal_packet)
    
    # Test address out of range (should be handled by memory model)
    try:
        overflow_packet = APBPacket(pwrite=1, paddr=0x10000, pwdata=0xDEADBEEF)
        await apb_master.send(overflow_packet)
        # Memory model may expand or handle gracefully
    except Exception as e:
        logger.info(f"Address overflow handled: {e}")
    
    # Test unaligned access
    unaligned_packet = APBPacket(pwrite=1, paddr=0x103, pwdata=0xCAFEBABE)
    await apb_master.send(unaligned_packet)
    
    await cmd_handler.stop()
```

### Performance and Timing Testing

```python
async def test_command_processing_performance(dut):
    # Large memory for performance testing
    memory_model = MemoryModel(num_lines=4096, bytes_per_line=4)
    cmd_handler = APBCommandHandler(dut, memory_model, logger)
    
    await cmd_handler.start()
    
    # APB master
    apb_master = APBMaster(dut, "PerfMaster", "apb_", dut.clk)
    
    # Measure processing time
    import time
    start_time = time.time()
    
    # Send many transactions
    num_transactions = 1000
    for i in range(num_transactions):
        addr = (i * 4) % 0x4000  # Stay within memory bounds
        data = i + 0x1000
        
        # Write
        write_packet = APBPacket(pwrite=1, paddr=addr, pwdata=data)
        await apb_master.send(write_packet)
        
        # Read back every 10th transaction
        if i % 10 == 0:
            read_packet = APBPacket(pwrite=0, paddr=addr)
            await apb_master.send(read_packet)
    
    end_time = time.time()
    duration = end_time - start_time
    
    logger.info(f"Processed {num_transactions} transactions in {duration:.2f} seconds")
    logger.info(f"Throughput: {num_transactions/duration:.2f} transactions/second")
    
    await cmd_handler.stop()
```

## Integration with Other Components

### With APB Components

```python
# Command handler works with any APB master/monitor
from CocoTBFramework.components.apb import APBMaster, APBMonitor

master = APBMaster(dut, "Master", "apb_", dut.clk)
monitor = APBMonitor(dut, "Monitor", "apb_", dut.clk)
cmd_handler = APBCommandHandler(dut, memory_model, logger)

await cmd_handler.start()
# Transactions from master are automatically processed
```

### With Memory Models

```python
# Command handler requires a MemoryModel instance
from CocoTBFramework.components.shared.memory_model import MemoryModel

# Different memory configurations
small_memory = MemoryModel(num_lines=64, bytes_per_line=4)    # 256 bytes
large_memory = MemoryModel(num_lines=4096, bytes_per_line=8)  # 32KB

cmd_handler = APBCommandHandler(dut, large_memory, logger)
```

### With Register Maps

```python
# Can be used with register map testing
from CocoTBFramework.tbclasses.apb.register_map import RegisterMap

reg_map = RegisterMap("registers.py", 32, 24, 0x1000000, logger)
memory_model = MemoryModel(num_lines=1024, bytes_per_line=4)
cmd_handler = APBCommandHandler(dut, memory_model, logger)

await cmd_handler.start()

# Generate and send register test transactions
transactions = reg_map.generate_read_transactions()
for transaction in transactions:
    await apb_master.send(transaction)
```

## Best Practices

### 1. **Proper Lifecycle Management**
```python
# Always start and stop properly
await cmd_handler.start()
try:
    # Test code
    pass
finally:
    await cmd_handler.stop()
```

### 2. **Memory Model Sizing**
```python
# Size memory appropriately for your test
max_addr = 0x10000  # Maximum address in test
lines_needed = (max_addr // 4) + 1
memory_model = MemoryModel(num_lines=lines_needed, bytes_per_line=4)
```

### 3. **Signal Verification**
```python
# Verify required signals exist
required_signals = [
    'o_cmd_valid', 'o_cmd_pwrite', 'o_cmd_paddr', 'o_cmd_pwdata',
    'i_cmd_ready', 'i_rsp_valid', 'i_rsp_prdata', 'o_rsp_ready'
]

for signal in required_signals:
    assert hasattr(dut, signal), f"Required signal {signal} not found"
```

### 4. **Error Handling**
```python
# Handle potential errors gracefully
try:
    await cmd_handler.start()
    # Test execution
except Exception as e:
    logger.error(f"Command handler error: {e}")
    raise
finally:
    await cmd_handler.stop()
```

The APB Command Handler provides essential infrastructure for testing APB slaves with command/response interfaces, enabling realistic processor-like behavior while maintaining proper protocol compliance and memory integration.