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

# apb_components.py

APB Protocol Components providing Monitor, Master, and Slave implementations for comprehensive APB verification. This module contains the core protocol-level components that handle signal-level communication and protocol compliance.

## Overview

The `apb_components.py` module provides three main classes that implement the APB protocol:
- **APBMonitor**: Observes and logs APB transactions
- **APBSlave**: Responds to APB transactions with memory backing
- **APBMaster**: Drives APB transactions with configurable timing

### Key Features
- **Full APB signal support** with optional signal handling
- **Memory model integration** for realistic slave behavior
- **Configurable timing randomization** for stress testing
- **Comprehensive error injection** and protocol validation
- **Transaction queuing and pipelining** for performance testing

## Constants and Mappings

### Signal Definitions

```python
# APB PWRITE mapping
pwrite = ['READ', 'WRITE']

# Required APB signals
apb_signals = [
    "PSEL",      # Peripheral select
    "PWRITE",    # Write enable
    "PENABLE",   # Enable signal
    "PADDR",     # Address bus
    "PWDATA",    # Write data bus
    "PRDATA",    # Read data bus
    "PREADY"     # Ready signal
]

# Optional APB signals
apb_optional_signals = [
    "PPROT",     # Protection control
    "PSLVERR",   # Slave error
    "PSTRB"      # Write strobes
]
```

## Core Classes

### APBMonitor

Bus monitor for observing and logging APB transactions without interfering with protocol operation.

#### Constructor

```python
APBMonitor(entity, title, prefix, clock, signals=None, bus_width=32, addr_width=12, log=None, **kwargs)
```

**Parameters:**
- `entity`: DUT entity to monitor
- `title`: Monitor identifier for logging
- `prefix`: Signal prefix for bus connection
- `clock`: Clock signal for synchronization
- `signals`: Custom signal list (default: standard APB signals)
- `bus_width`: Data bus width in bits (default: 32)
- `addr_width`: Address bus width in bits (default: 12)
- `log`: Logger instance (default: entity logger)

```python
# Create APB monitor
monitor = APBMonitor(
    entity=dut,
    title="APB_Monitor",
    prefix="apb_",
    clock=dut.clk,
    bus_width=32,
    addr_width=16
)
```

#### Methods

##### `is_signal_present(signal_name) -> bool`
Check if an optional signal is present and connected.

```python
if monitor.is_signal_present('PSLVERR'):
    # Handle slave error signal
    pass
```

##### `print(transaction)`
Print formatted transaction information to log.

**Parameters:**
- `transaction`: APBPacket transaction to display

```python
monitor.print(packet)  # Logs transaction details
```

#### Transaction Detection

The monitor automatically detects valid APB transactions when:
- `PSEL` is asserted
- `PENABLE` is asserted  
- `PREADY` is asserted
- All signals have resolvable values

### APBSlave

APB slave implementation with memory backing and configurable response behavior.

#### Constructor

```python
APBSlave(entity, title, prefix, clock, registers, signals=None, bus_width=32, addr_width=12, randomizer=None, log=None, error_overflow=False, **kwargs)
```

**Parameters:**
- `entity`: DUT entity to connect to
- `title`: Slave identifier for logging
- `prefix`: Signal prefix for bus connection
- `clock`: Clock signal for synchronization
- `registers`: Initial register values or register count
- `signals`: Custom signal list (default: standard APB signals)
- `bus_width`: Data bus width in bits (default: 32)
- `addr_width`: Address bus width in bits (default: 12)
- `randomizer`: Timing randomizer (default: FlexRandomizer)
- `log`: Logger instance (default: entity logger)
- `error_overflow`: Generate errors on address overflow (default: False)

```python
# Create APB slave with 256 registers
registers = [0] * 1024  # 256 32-bit registers
slave = APBSlave(
    entity=dut,
    title="APB_Slave",
    prefix="apb_",
    clock=dut.clk,
    registers=registers,
    bus_width=32,
    addr_width=16,
    error_overflow=True
)
```

#### Methods

##### `set_randomizer(randomizer)`
Update the timing randomizer for ready signal delays.

```python
new_randomizer = FlexRandomizer({
    'ready': ([[0, 2], [5, 10]], [8, 1]),
    'error': ([[0, 0], [1, 1]], [20, 1])
})
slave.set_randomizer(new_randomizer)
```

##### `dump_registers()`
Display current register contents to log.

```python
slave.dump_registers()  # Shows memory dump
```

##### `reset_bus()`
Reset all bus outputs to default values.

```python
await slave.reset_bus()
```

##### `reset_registers()`
Reset all registers to their preset values.

```python
slave.reset_registers()
```

#### Response Behavior

The slave provides configurable response timing:
- **Ready Delay**: Configurable cycles before asserting PREADY
- **Error Injection**: Random or deterministic error generation
- **Memory Expansion**: Automatic memory expansion on overflow

### APBMaster

APB master implementation that drives transactions with configurable timing and queuing.

#### Constructor

```python
APBMaster(entity, title, prefix, clock, signals=None, bus_width=32, addr_width=12, randomizer=None, log=None, **kwargs)
```

**Parameters:**
- `entity`: DUT entity to drive
- `title`: Master identifier for logging
- `prefix`: Signal prefix for bus connection
- `clock`: Clock signal for synchronization
- `signals`: Custom signal list (default: standard APB signals)
- `bus_width`: Data bus width in bits (default: 32)
- `addr_width`: Address bus width in bits (default: 12)
- `randomizer`: Timing randomizer (default: FlexRandomizer)
- `log`: Logger instance (default: entity logger)

```python
# Create APB master
master = APBMaster(
    entity=dut,
    title="APB_Master",
    prefix="apb_",
    clock=dut.clk,
    bus_width=32,
    addr_width=16
)
```

#### Methods

##### `set_randomizer(randomizer)`
Update the timing randomizer for transaction delays.

```python
timing_randomizer = FlexRandomizer({
    'psel': ([[0, 0], [1, 5]], [6, 1]),      # Mostly immediate PSEL
    'penable': ([[0, 0], [1, 2]], [4, 1])    # Minimal PENABLE delay
})
master.set_randomizer(timing_randomizer)
```

##### `reset_bus()`
Reset all bus outputs and clear transaction queue.

```python
await master.reset_bus()
```

##### `send(transaction)`
Add transaction to transmission queue.

**Parameters:**
- `transaction`: APBPacket to transmit

```python
packet = APBPacket(pwrite=1, paddr=0x100, pwdata=0xDEADBEEF)
await master.send(packet)
```

##### `busy_send(transaction)`
Send transaction and wait for completion.

```python
await master.busy_send(packet)  # Blocks until transaction completes
```

#### Transaction Pipeline

The master implements a transaction pipeline:
1. **Queue Management**: Transactions queued for transmission
2. **Signal Setup**: Configure address, data, and control signals
3. **Protocol Phases**: Handle PSEL and PENABLE timing
4. **Completion**: Wait for PREADY and capture response

## Usage Patterns

### Basic Monitor Setup

```python
import cocotb
from cocotb.triggers import RisingEdge
from CocoTBFramework.components.apb.apb_components import APBMonitor

@cocotb.test()
async def monitor_test(dut):
    # Create monitor
    monitor = APBMonitor(
        entity=dut,
        title="Protocol_Monitor", 
        prefix="apb_",
        clock=dut.clk,
        bus_width=32
    )
    
    # Add callback for transaction observation
    def transaction_callback(packet):
        print(f"Observed: {packet.formatted(compact=True)}")
    
    monitor.add_callback(transaction_callback)
    
    # Monitor runs automatically
    await Timer(1000, units='ns')
```

### Master-Slave Communication

```python
async def master_slave_test(dut):
    # Create master and slave
    master = APBMaster(dut, "Master", "m_apb_", dut.clk)
    slave = APBSlave(dut, "Slave", "s_apb_", dut.clk, registers=256)
    
    # Reset both components
    await master.reset_bus()
    await slave.reset_bus()
    
    # Write operation
    write_packet = APBPacket(
        pwrite=1,
        paddr=0x100,
        pwdata=0x12345678,
        pstrb=0xF
    )
    await master.send(write_packet)
    
    # Read operation
    read_packet = APBPacket(
        pwrite=0,
        paddr=0x100
    )
    await master.send(read_packet)
    
    # Wait for completion
    while master.transfer_busy:
        await RisingEdge(dut.clk)
```

### Advanced Timing Configuration

```python
def setup_timing_profiles():
    # Fast profile for performance testing
    fast_profile = FlexRandomizer({
        'psel': ([[0, 0]], [1]),           # No PSEL delay
        'penable': ([[0, 0]], [1]),        # No PENABLE delay
        'ready': ([[0, 0]], [1]),          # Immediate ready
        'error': ([[0, 0]], [1])           # No errors
    })
    
    # Stress profile for robustness testing
    stress_profile = FlexRandomizer({
        'psel': ([[0, 0], [1, 10]], [3, 1]),     # Variable PSEL delay
        'penable': ([[0, 1], [2, 5]], [2, 1]),   # Variable PENABLE delay
        'ready': ([[0, 5], [10, 20]], [4, 1]),   # Variable ready delay
        'error': ([[0, 0], [1, 1]], [10, 1])     # 10% error rate
    })
    
    return fast_profile, stress_profile

async def timing_test(dut):
    fast_profile, stress_profile = setup_timing_profiles()
    
    master = APBMaster(dut, "Master", "apb_", dut.clk)
    slave = APBSlave(dut, "Slave", "apb_", dut.clk, registers=1024)
    
    # Test with fast timing
    master.set_randomizer(fast_profile)
    slave.set_randomizer(fast_profile)
    
    # Run fast test sequence
    await run_test_sequence(master, fast_transactions)
    
    # Switch to stress timing
    master.set_randomizer(stress_profile)
    slave.set_randomizer(stress_profile)
    
    # Run stress test sequence
    await run_test_sequence(master, stress_transactions)
```

### Error Injection Testing

```python
async def error_injection_test(dut):
    # Create slave with error injection
    error_randomizer = FlexRandomizer({
        'ready': ([[1, 3], [5, 10]], [3, 1]),
        'error': ([[0, 0], [1, 1]], [4, 1])  # 20% error rate
    })
    
    slave = APBSlave(
        dut, "Error_Slave", "apb_", dut.clk,
        registers=256,
        randomizer=error_randomizer,
        error_overflow=True
    )
    
    master = APBMaster(dut, "Master", "apb_", dut.clk)
    
    # Test normal addresses
    for addr in range(0, 64, 4):
        packet = APBPacket(pwrite=1, paddr=addr, pwdata=addr*2)
        await master.send(packet)
    
    # Test overflow addresses (should generate errors)
    for addr in range(0x1000, 0x1040, 4):
        packet = APBPacket(pwrite=1, paddr=addr, pwdata=0xBAADF00D)
        await master.send(packet)
```

### Register Verification

```python
async def register_verification(dut):
    slave = APBSlave(dut, "Register_Slave", "apb_", dut.clk, registers=1024)
    master = APBMaster(dut, "Master", "apb_", dut.clk)
    
    # Test register read/write
    test_patterns = [0x00000000, 0xFFFFFFFF, 0x55555555, 0xAAAAAAAA]
    
    for i, pattern in enumerate(test_patterns):
        addr = i * 4
        
        # Write pattern
        write_packet = APBPacket(pwrite=1, paddr=addr, pwdata=pattern)
        await master.send(write_packet)
        
        # Read back
        read_packet = APBPacket(pwrite=0, paddr=addr)
        await master.send(read_packet)
        
        # Verify in slave memory
        await Timer(100, units='ns')
        slave.dump_registers()
```

### Performance Testing

```python
async def performance_test(dut):
    # Configure for maximum performance
    fast_randomizer = FlexRandomizer({
        'psel': ([[0, 0]], [1]),
        'penable': ([[0, 0]], [1]),
        'ready': ([[0, 0]], [1]),
        'error': ([[0, 0]], [1])
    })
    
    master = APBMaster(dut, "Perf_Master", "apb_", dut.clk, randomizer=fast_randomizer)
    slave = APBSlave(dut, "Perf_Slave", "apb_", dut.clk, registers=1024, randomizer=fast_randomizer)
    
    # Measure transaction throughput
    start_time = get_sim_time('ns')
    
    # Send 1000 back-to-back transactions
    for i in range(1000):
        packet = APBPacket(pwrite=1, paddr=(i*4) % 1024, pwdata=i)
        await master.send(packet)
    
    # Wait for completion
    while master.transfer_busy:
        await RisingEdge(dut.clk)
    
    end_time = get_sim_time('ns')
    duration = end_time - start_time
    
    print(f"1000 transactions completed in {duration} ns")
    print(f"Throughput: {1000 * 1e9 / duration:.2f} transactions/second")
```

## Integration with Framework

### Memory Model Integration

The APBSlave uses the shared MemoryModel for realistic memory behavior:

```python
# Memory model provides:
# - Byte-level access control
# - Strobe mask support
# - Access tracking and coverage
# - Boundary checking
# - Memory expansion
```

### Packet Integration

Components work seamlessly with APBPacket:

```python
# Automatic field extraction and validation
# Protocol compliance checking
# Transaction correlation and tracking
```

### Randomization Integration

Uses FlexRandomizer for comprehensive timing control:

```python
# Configurable delay distributions
# Error injection patterns
# Protocol timing stress testing
```

## Best Practices

### 1. **Use Appropriate Randomization**
```python
# Development/debug: minimal delays
debug_randomizer = FlexRandomizer({
    'psel': ([[0, 0]], [1]),
    'penable': ([[0, 0]], [1]),
    'ready': ([[0, 1]], [1])
})

# Stress testing: variable delays
stress_randomizer = FlexRandomizer({
    'psel': ([[0, 0], [1, 10]], [7, 1]),
    'penable': ([[0, 1], [2, 5]], [3, 1]),
    'ready': ([[0, 5], [10, 25]], [5, 1])
})
```

### 2. **Handle Optional Signals**
```python
# Always check signal presence
if slave.is_signal_present('PSLVERR'):
    # Handle slave error
    pass

if master.is_signal_present('PSTRB'):
    # Use write strobes
    packet.pstrb = 0xF
```

### 3. **Reset Components Properly**
```python
# Reset in correct order
await master.reset_bus()
await slave.reset_bus()
slave.reset_registers()
```

### 4. **Monitor Transaction Completion**
```python
# For performance-critical tests
await master.busy_send(packet)

# For pipelined operation
await master.send(packet)
while master.transfer_busy:
    await RisingEdge(dut.clk)
```

### 5. **Use Memory Dumps for Debug**
```python
# Regular memory verification
slave.dump_registers()

# After test completion
print(f"Slave processed {slave.count} transactions")
```

The APB components provide a comprehensive foundation for APB protocol verification, from basic functional testing to advanced stress testing and performance analysis.