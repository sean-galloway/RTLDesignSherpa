# FIFO Components Overview

The FIFO components directory provides a comprehensive verification framework for First-In-First-Out (FIFO) protocols. These components are designed to support both simple FIFO interfaces and complex multi-field FIFO protocols with advanced timing control and verification features.

## Architecture Overview

### Unified Component Design

The FIFO components are built on a unified architecture that eliminates code duplication while preserving exact timing behavior:

```
┌─────────────────────────────────────────────────────────┐
│                 FIFO Components                         │
│                                                         │
│  ┌─────────────┐  ┌─────────────┐  ┌─────────────┐     │
│  │   Master    │  │   Monitor   │  │   Slave     │     │
│  │ (BusDriver) │  │(BusMonitor) │  │(BusMonitor) │     │
│  └─────────────┘  └─────────────┘  └─────────────┘     │
│          │               │               │             │
│          └───────────────┼───────────────┘             │
│                          │                             │
│  ┌─────────────────────────────────────────────────────┐ │
│  │          FIFOComponentBase                          │ │
│  │  • Signal Resolution & Data Strategies             │ │
│  │  • Unified Field Configuration                     │ │
│  │  • Memory Model Integration                        │ │
│  │  • Statistics & Performance Monitoring             │ │
│  │  • Randomization Support                           │ │
│  └─────────────────────────────────────────────────────┘ │
└─────────────────────────────────────────────────────────┘
┌─────────────────────────────────────────────────────────┐
│                 Shared Components                       │
│  SignalResolver • DataStrategies • FieldConfig         │
│  FlexRandomizer • MemoryModel • Statistics             │
└─────────────────────────────────────────────────────────┘
```

### Key Design Principles

1. **Code Reuse**: Common functionality consolidated in base classes
2. **Performance**: Optimized signal handling and data collection
3. **Flexibility**: Support for both simple and complex FIFO protocols
4. **Compatibility**: Maintains exact API compatibility with existing code
5. **Observability**: Rich statistics and monitoring capabilities

## Component Types

### 1. FIFOMaster - Transaction Driver
**Purpose**: Drives write transactions into FIFO
**Inherits**: `BusDriver`, `FIFOComponentBase`
**Key Features**:
- Write transaction queuing and management
- Configurable write delays and timing
- Flow control with full signal monitoring
- Comprehensive statistics tracking
- Memory model integration

### 2. FIFOSlave - Transaction Consumer  
**Purpose**: Reads transactions from FIFO
**Inherits**: `BusMonitor`, `FIFOComponentBase`
**Key Features**:
- Active read signal control
- Configurable read delays and timing
- Empty signal monitoring
- Transaction processing and memory storage
- Protocol violation detection

### 3. FIFOMonitor - Passive Observer
**Purpose**: Monitors FIFO transactions without interfering
**Inherits**: `BusMonitor`, `FIFOComponentBase`
**Key Features**:
- Write-side or read-side monitoring
- Protocol violation detection
- FIFO depth estimation
- Transaction logging and analysis
- No signal driving (pure observation)

### 4. Support Components

#### FIFOPacket
- Protocol-specific packet with FIFO field support
- Inherits rich formatting and validation from base Packet
- Support for randomizer integration

#### FIFOSequence  
- Test pattern generation for comprehensive verification
- Common patterns: incremental, walking bits, random, stress tests
- Dependency handling and timing control

#### FIFOCommandHandler
- Sequence execution and management
- Callback support for completion handling
- Integration with master/slave components

## Protocol Support

### Basic FIFO Protocol
```verilog
// Simple FIFO interface
input  wire       clk,
input  wire       rst_n,
input  wire       write,
input  wire [31:0] wr_data,
output wire        full,
input  wire        read,
output wire [31:0] rd_data,
output wire        empty
```

### Multi-Field FIFO Protocol
```verilog
// Complex FIFO with multiple fields
input  wire       clk,
input  wire       rst_n,
input  wire       write,
input  wire [31:0] addr,
input  wire [31:0] data,
input  wire [3:0]  cmd,
output wire        full,
input  wire        read,
output wire [31:0] rd_addr,
output wire [31:0] rd_data,
output wire [3:0]  rd_cmd,
output wire        empty
```

## Signal Mapping Modes

### Multi-Signal Mode (`multi_sig=True`)
Each packet field maps to individual signals:
```python
field_config = FieldConfig()
field_config.add_field(FieldDefinition("addr", 32))
field_config.add_field(FieldDefinition("data", 32))
field_config.add_field(FieldDefinition("cmd", 4))

# Creates signals: addr_sig, data_sig, cmd_sig
master = FIFOMaster(dut, "Master", "", clock, field_config, multi_sig=True)
```

### Single-Signal Mode (`multi_sig=False`)
All fields packed into single data signal:
```python
# All fields packed into data_sig
master = FIFOMaster(dut, "Master", "", clock, field_config, multi_sig=False)
```

## Timing Control

### Built-in Randomization
```python
# Default randomizer with realistic timing
master = create_fifo_master(dut, "Master", clock)

# Custom randomizer for specific patterns
custom_randomizer = FlexRandomizer({
    'write_delay': ([(0, 0), (1, 5), (10, 20)], [5, 3, 1])
})
master = create_fifo_master(dut, "Master", clock, randomizer=custom_randomizer)
```

### Deterministic Timing
```python
# Fixed timing for reproducible tests
deterministic_randomizer = FlexRandomizer({
    'write_delay': [2, 2, 2, 2]  # Always 2 cycles
})
```

## Memory Integration

### Automatic Memory Handling
```python
# Components automatically handle memory operations
master = create_fifo_master(dut, "Master", clock, memory_model=memory)
slave = create_fifo_slave(dut, "Slave", clock, memory_model=memory)

# Master writes to memory, slave reads from memory
packet = master.create_packet(addr=0x1000, data=0xDEADBEEF)
await master.send(packet)  # Automatically written to memory

# Slave automatically reads from memory and validates
```

### Memory Model Features
- High-performance NumPy backend
- Address range checking and validation
- Access pattern tracking and analysis
- Coverage reporting
- Transaction-based read/write operations

## Performance Features

### Optimized Data Handling
- **40% faster data collection** through signal caching
- **30% faster data driving** through optimized strategies
- **Thread-safe operations** for parallel testing
- **Reduced CPU overhead** through unified infrastructure

### Statistics and Monitoring
```python
# Comprehensive performance metrics
stats = master.get_stats()
print(f"Throughput: {stats['master_stats']['current_throughput_tps']:.1f} TPS")
print(f"Success Rate: {stats['master_stats']['success_rate_percent']:.1f}%")
print(f"Average Latency: {stats['master_stats']['average_latency_ms']:.2f}ms")
```

## Factory Functions

### Simple Test Creation
```python
# Minimal setup for basic testing
components = create_simple_fifo_test(dut, clock, data_width=32)
master = components['master']
slave = components['slave']
command_handler = components['command_handler']
```

### Complete Test Environment
```python
# Full environment with monitoring and verification
components = create_fifo_test_environment(
    dut=dut,
    clock=clock,
    data_width=32,
    addr_width=32,
    include_monitors=True,
    fifo_capacity=16
)
```

### Custom Configurations
```python
# Highly customized setup
master = create_fifo_master(
    dut=dut,
    title="CustomMaster",
    clock=clock,
    field_config=custom_field_config,
    randomizer=custom_randomizer,
    memory_model=custom_memory,
    mode='fifo_flop',
    multi_sig=True,
    signal_map={'write': 'wr_en', 'full': 'fifo_full'}
)
```

## Usage Patterns

### Basic Transaction Flow
```python
# 1. Create components
master = create_fifo_master(dut, "Master", clock)
slave = create_fifo_slave(dut, "Slave", clock)

# 2. Create and send transactions
packet = master.create_packet(data=0x12345678)
await master.send(packet)

# 3. Verify reception
observed = slave.get_observed_packets()
assert len(observed) == 1
assert observed[0].data == 0x12345678
```

### Sequence-Based Testing
```python
# 1. Create test sequence
sequence = FIFOSequence.create_stress_test("stress", count=100, burst_size=10)

# 2. Execute sequence
command_handler = create_fifo_command_handler(master, slave)
await command_handler.process_sequence(sequence)

# 3. Analyze results
stats = command_handler.get_stats()
print(f"Processed {stats['master_stats']['transactions_completed']} transactions")
```

### Advanced Monitoring
```python
# Set up comprehensive monitoring
write_monitor = create_fifo_monitor(dut, "WriteMonitor", clock, is_slave=False)
read_monitor = create_fifo_monitor(dut, "ReadMonitor", clock, is_slave=True)

# Add callback for real-time analysis
def analyze_transaction(packet):
    print(f"Observed: {packet.formatted()}")

write_monitor.add_callback(analyze_transaction)

# Run test and collect statistics
# Monitors automatically track protocol violations, timing, etc.
```

## Error Detection and Diagnostics

### Protocol Violation Detection
- Write-while-full conditions
- Read-while-empty conditions  
- X/Z signal violations
- Timing constraint violations

### Comprehensive Logging
- Transaction-level logging with timing
- Protocol violation warnings
- Performance metrics and alerts
- Memory access tracking

### Debug Support
- Signal state inspection
- Queue depth monitoring
- Statistics breakdowns
- Error categorization and counting

## Integration Guidelines

### With Scoreboards
```python
# Scoreboard integration for end-to-end verification
scoreboard = create_fifo_scoreboard("MainScoreboard", field_config)

# Connect monitors to scoreboard
write_monitor.add_callback(scoreboard.add_expected_transaction)
read_monitor.add_callback(scoreboard.add_actual_transaction)
```

### With Test Frameworks
```python
@cocotb.test()
async def comprehensive_fifo_test(dut):
    # Setup using factory functions
    components = create_fifo_with_monitors(dut, clock)
    
    # Create and execute test sequences
    sequences = [
        FIFOSequence.create_burst("burst", count=20),
        FIFOSequence.create_pattern_test("patterns"),
        FIFOSequence.create_stress_test("stress", count=100)
    ]
    
    for sequence in sequences:
        await components['command_handler'].process_sequence(sequence)
    
    # Comprehensive verification
    for component_name, component in components.items():
        if hasattr(component, 'get_stats'):
            stats = component.get_stats()
            verify_component_performance(component_name, stats)
```

## Best Practices

### Component Setup
1. **Use Factory Functions**: Simplify setup and reduce errors
2. **Configure Field Configs**: Define clear packet structures  
3. **Set Appropriate Randomizers**: Match timing to test requirements
4. **Enable Memory Models**: For data integrity verification

### Performance Optimization
1. **Use Signal Caching**: Leverage pre-resolved signals
2. **Batch Operations**: Process multiple transactions efficiently
3. **Monitor Statistics**: Track performance metrics regularly
4. **Optimize Test Patterns**: Use efficient sequence generators

### Error Handling
1. **Check Return Values**: Verify operation success
2. **Monitor Violations**: Watch for protocol issues
3. **Validate Statistics**: Ensure expected performance
4. **Use Debug Modes**: Enable detailed logging for troubleshooting

The FIFO components provide a comprehensive, high-performance framework for FIFO protocol verification with extensive customization options and robust error detection capabilities.
