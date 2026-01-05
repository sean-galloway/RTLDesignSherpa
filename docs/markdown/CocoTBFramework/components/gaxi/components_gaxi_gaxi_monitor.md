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

# gaxi_monitor.py

GAXI Monitor implementation using unified base functionality. Preserves exact timing-critical cocotb methods and external API while eliminating code duplication through inheritance from unified base classes.

## Overview

The `GAXIMonitor` class provides:
- **Pure monitoring functionality** with no signal driving
- **Master-side or slave-side monitoring** based on is_slave parameter
- **Protocol violation detection** and reporting
- **Handshake tracking** with precise timing
- **Inherited functionality** from GAXIMonitorBase for common operations
- **Mode-specific data sampling** with corrected timing

Inherits all common functionality from GAXIMonitorBase including signal resolution, data collection, packet management, and memory integration.

## Class

### GAXIMonitor

```python
class GAXIMonitor(GAXIMonitorBase):
    def __init__(self, dut, title, prefix, clock, field_config, is_slave=False,
                 bus_name='', pkt_prefix='', multi_sig=False,
                 log=None, super_debug=False, signal_map=None, **kwargs)
```

**Parameters:**
- `dut`: Device under test
- `title`: Component title/name
- `prefix`: Bus prefix
- `clock`: Clock signal
- `field_config`: Field configuration
- `is_slave`: If True, monitor slave side; if False, monitor master side
- `mode`: GAXI mode ('skid', 'fifo_mux', 'fifo_flop') - for DUT parameter only
- `bus_name`: Bus/channel name
- `pkt_prefix`: Packet field prefix
- `multi_sig`: Whether using multi-signal mode
- `log`: Logger instance
- `super_debug`: Enable detailed debugging
- `signal_map`: Optional manual signal mapping override
- `**kwargs`: Additional arguments

## Data Sampling Rules

The GAXIMonitor uses corrected sampling timing based on mode and monitoring side:

### Master Side Monitoring (`is_slave=False`)
- **All modes**: Always sample immediately when handshake detected
- **Rationale**: Master side signals are stable at handshake time
- **Performance**: Lowest latency monitoring

### Slave Side Monitoring (`is_slave=True`)
- **Skid mode**: Sample immediately when handshake detected
- **FIFO MUX mode**: Sample immediately when handshake detected  
- **FIFO FLOP mode**: Delay capture by one cycle after handshake
- **Rationale**: Matches DUT internal timing for different implementations

## Core Methods

### Inherited Methods

GAXIMonitor inherits all methods from GAXIMonitorBase:
- `create_packet(**field_values)` - Create packets
- `get_observed_packets(count=None)` - Get observed transactions
- `clear_queue()` - Clear observation queue
- `handle_memory_write(packet)` - Memory integration
- `handle_memory_read(packet)` - Memory integration
- `get_base_stats()` - Statistics collection

### Monitor-Specific Methods

#### `get_stats()`
Get comprehensive statistics including monitor-specific information.

**Returns:** Dictionary containing all statistics

```python
stats = monitor.get_stats()
print(f"Monitor type: {stats['monitor_type']}")  # 'master' or 'slave'
print(f"Observed packets: {stats['observed_packets']}")
print(f"Protocol violations: {stats['monitor_stats']['protocol_violations']}")
```

## Usage Patterns

### Basic Master Side Monitoring

```python
import cocotb
from cocotb.triggers import Timer
from CocoTBFramework.components.gaxi import GAXIMonitor
from CocoTBFramework.shared.field_config import FieldConfig

@cocotb.test()
async def test_master_monitoring(dut):
    clock = dut.clk
    
    # Create field configuration
    field_config = FieldConfig()
    field_config.add_field(FieldDefinition("addr", 32, format="hex"))
    field_config.add_field(FieldDefinition("data", 32, format="hex"))
    
    # Create master side monitor
    master_monitor = GAXIMonitor(
        dut=dut,
        title="MasterMonitor",
        prefix="m_",  # Monitor master interface
        clock=clock,
        field_config=field_config,
        is_slave=False,  # Monitor master side
        mode='skid'
    )
    
    # Add callback to process observed transactions
    def log_transaction(packet):
        print(f"Master sent: addr=0x{packet.addr:X}, data=0x{packet.data:X}")
    
    master_monitor.add_callback(log_transaction)
    
    # Run test and let monitor observe
    await Timer(1000, units='ns')
    
    # Check observed transactions
    packets = master_monitor.get_observed_packets()
    print(f"Master monitor observed {len(packets)} transactions")
```

### Basic Slave Side Monitoring

```python
@cocotb.test()
async def test_slave_monitoring(dut):
    clock = dut.clk
    
    # Create field configuration
    field_config = FieldConfig()
    field_config.add_field(FieldDefinition("addr", 32, format="hex"))
    field_config.add_field(FieldDefinition("data", 32, format="hex"))
    
    # Create slave side monitor with FIFO FLOP mode
    slave_monitor = GAXIMonitor(
        dut=dut,
        title="SlaveMonitor", 
        prefix="s_",  # Monitor slave interface
        clock=clock,
        field_config=field_config,
        is_slave=True,   # Monitor slave side
        mode='fifo_flop' # DUT uses registered interface
    )
    
    # Add callback to process observed transactions
    def process_slave_transaction(packet):
        print(f"Slave received: addr=0x{packet.addr:X}, data=0x{packet.data:X}")
        
        # Additional processing
        if packet.addr >= 0x8000:
            print("  → High address region")
    
    slave_monitor.add_callback(process_slave_transaction)
    
    # Run test
    await Timer(1000, units='ns')
    
    # Analyze slave activity
    packets = slave_monitor.get_observed_packets()
    print(f"Slave monitor observed {len(packets)} transactions")
```

### Dual Monitor Setup

```python
@cocotb.test()
async def test_dual_monitoring(dut):
    clock = dut.clk
    field_config = create_field_config()
    
    # Monitor both sides of the interface
    master_monitor = GAXIMonitor(
        dut=dut,
        title="MasterSideMonitor",
        prefix="m_",
        clock=clock,
        field_config=field_config,
        is_slave=False  # Master side
    )
    
    slave_monitor = GAXIMonitor(
        dut=dut,
        title="SlaveSideMonitor", 
        prefix="s_",
        clock=clock,
        field_config=field_config,
        is_slave=True   # Slave side
    )
    
    # Track transactions on both sides
    master_transactions = []
    slave_transactions = []
    
    def track_master(packet):
        master_transactions.append(packet)
        print(f"Master → Slave: {packet.formatted(compact=True)}")
    
    def track_slave(packet):
        slave_transactions.append(packet)
        print(f"Slave ← Master: {packet.formatted(compact=True)}")
    
    master_monitor.add_callback(track_master)
    slave_monitor.add_callback(track_slave)
    
    # Run test
    await Timer(2000, units='ns')
    
    # Compare transaction counts
    print(f"Master side: {len(master_transactions)} transactions")
    print(f"Slave side: {len(slave_transactions)} transactions")
    
    # Verify transaction matching
    assert len(master_transactions) == len(slave_transactions), \
        "Transaction count mismatch between master and slave sides"
```

### Protocol Violation Monitoring

```python
@cocotb.test()
async def test_protocol_violations(dut):
    # Create monitor with protocol checking
    monitor = GAXIMonitor(
        dut=dut,
        title="ProtocolMonitor",
        prefix="",
        clock=clock,
        field_config=field_config,
        is_slave=False,
        super_debug=True  # Enable detailed logging
    )
    
    # Track protocol violations
    violations = []
    
    def check_protocol(packet):
        """Check for protocol violations in observed transactions"""
        # Check address alignment
        if hasattr(packet, 'addr') and packet.addr % 4 != 0:
            violation = f"Unaligned address: 0x{packet.addr:X}"
            violations.append(violation)
            print(f"VIOLATION: {violation}")
        
        # Check for X/Z values
        for field_name in ['addr', 'data']:
            if hasattr(packet, field_name):
                value = getattr(packet, field_name)
                if value == -1:  # X/Z represented as -1
                    violation = f"X/Z value in {field_name}"
                    violations.append(violation)
                    print(f"VIOLATION: {violation}")
    
    monitor.add_callback(check_protocol)
    
    # Run test
    await Timer(1000, units='ns')
    
    # Report violations
    if violations:
        print(f"Detected {len(violations)} protocol violations:")
        for violation in violations:
            print(f"  - {violation}")
    else:
        print("No protocol violations detected")
    
    # Get monitor statistics
    stats = monitor.get_stats()
    print(f"Monitor statistics: {stats['monitor_stats']}")
```

### Performance Monitoring

```python
@cocotb.test()
async def test_performance_monitoring(dut):
    monitor = GAXIMonitor(dut, "PerfMonitor", "", clock, field_config)
    
    # Performance tracking
    transaction_times = []
    inter_transaction_times = []
    last_time = 0
    
    def track_performance(packet):
        current_time = get_sim_time('ns')
        transaction_times.append(current_time)
        
        if last_time > 0:
            inter_time = current_time - last_time
            inter_transaction_times.append(inter_time)
        
        nonlocal last_time
        last_time = current_time
    
    monitor.add_callback(track_performance)
    
    # Run test
    await Timer(5000, units='ns')
    
    # Analyze performance
    if inter_transaction_times:
        avg_interval = sum(inter_transaction_times) / len(inter_transaction_times)
        throughput = 1e9 / avg_interval if avg_interval > 0 else 0
        
        print(f"Performance Analysis:")
        print(f"  Transactions: {len(transaction_times)}")
        print(f"  Average interval: {avg_interval:.2f} ns")
        print(f"  Throughput: {throughput:.1f} TPS")
        print(f"  Min interval: {min(inter_transaction_times):.2f} ns")
        print(f"  Max interval: {max(inter_transaction_times):.2f} ns")
```

### Mode-Specific Configuration

```python
def create_mode_specific_monitors(dut, clock, field_config):
    """Create monitors for different DUT modes"""
    
    monitors = {}
    
    # Skid mode monitor (immediate capture)
    monitors['skid'] = GAXIMonitor(
        dut=dut,
        title="SkidMonitor",
        prefix="skid_",
        clock=clock,
        field_config=field_config,
        is_slave=True,
        mode='skid'
    )
    
    # FIFO MUX mode monitor (immediate capture)
    monitors['fifo_mux'] = GAXIMonitor(
        dut=dut,
        title="FifoMuxMonitor",
        prefix="mux_",
        clock=clock,
        field_config=field_config,
        is_slave=True,
        mode='fifo_mux'
    )
    
    # FIFO FLOP mode monitor (delayed capture)
    monitors['fifo_flop'] = GAXIMonitor(
        dut=dut,
        title="FifoFlopMonitor", 
        prefix="flop_",
        clock=clock,
        field_config=field_config,
        is_slave=True,
        mode='fifo_flop'  # One cycle delay for data capture
    )
    
    return monitors

@cocotb.test()
async def test_mode_specific_monitoring(dut):
    monitors = create_mode_specific_monitors(dut, clock, field_config)
    
    # Add same callback to all monitors
    def log_transaction(packet):
        print(f"Transaction: {packet.formatted(compact=True)}")
    
    for mode, monitor in monitors.items():
        monitor.add_callback(log_transaction)
    
    # Run test
    await Timer(1000, units='ns')
    
    # Compare results across modes
    for mode, monitor in monitors.items():
        packets = monitor.get_observed_packets()
        stats = monitor.get_stats()
        print(f"{mode} mode: {len(packets)} packets, {stats['monitor_type']} side")
```

### Integration with Scoreboards

```python
from CocoTBFramework.scoreboards.gaxi_scoreboard import GAXIScoreboard

@cocotb.test()
async def test_scoreboard_integration(dut):
    # Create scoreboard
    scoreboard = GAXIScoreboard("TestScoreboard", field_config, log=log)
    
    # Create monitors
    master_monitor = GAXIMonitor(dut, "MasterMon", "m_", clock, field_config, 
                                is_slave=False)
    slave_monitor = GAXIMonitor(dut, "SlaveMon", "s_", clock, field_config,
                               is_slave=True)
    
    # Connect monitors to scoreboard
    master_monitor.add_callback(scoreboard.add_expected_transaction)
    slave_monitor.add_callback(scoreboard.add_actual_transaction)
    
    # Run test
    await Timer(2000, units='ns')
    
    # Check scoreboard results
    scoreboard_stats = scoreboard.get_stats()
    print(f"Scoreboard: {scoreboard_stats['matches']} matches, "
          f"{scoreboard_stats['mismatches']} mismatches")
    
    # Verify all transactions matched
    assert scoreboard_stats['mismatches'] == 0, "Transaction mismatches detected"
```

### Memory Validation Monitoring

```python
@cocotb.test()
async def test_memory_validation(dut):
    # Create memory model for validation
    memory = MemoryModel(num_lines=256, bytes_per_line=4, log=log)
    
    # Create monitor with memory integration
    monitor = GAXIMonitor(
        dut=dut,
        title="MemoryMonitor",
        prefix="",
        clock=clock,
        field_config=field_config,
        memory_model=memory,
        is_slave=True
    )
    
    # Track memory operations
    def validate_memory_transaction(packet):
        """Validate transactions against memory model"""
        if hasattr(packet, 'cmd'):
            if packet.cmd == 2:  # Write
                success = monitor.handle_memory_write(packet)
                if success:
                    print(f"Memory write: addr=0x{packet.addr:X}, "
                          f"data=0x{packet.data:X}")
                else:
                    print(f"Memory write failed: addr=0x{packet.addr:X}")
            
            elif packet.cmd == 1:  # Read
                success, data = monitor.handle_memory_read(packet)
                if success:
                    print(f"Memory read: addr=0x{packet.addr:X}, "
                          f"data=0x{data:X}")
                    # Validate read data if available
                    if hasattr(packet, 'data') and packet.data != data:
                        print(f"  WARNING: Expected 0x{data:X}, "
                              f"got 0x{packet.data:X}")
    
    monitor.add_callback(validate_memory_transaction)
    
    # Run test
    await Timer(1000, units='ns')
    
    # Get memory statistics
    stats = monitor.get_stats()
    if 'memory_stats' in stats:
        memory_stats = stats['memory_stats']
        print(f"Memory operations: reads={memory_stats['reads']}, "
              f"writes={memory_stats['writes']}")
```

## Advanced Features

### Custom Signal Mapping

```python
# For non-standard signal names
signal_map = {
    'valid': 'master_transaction_valid',
    'ready': 'slave_ready_signal',
    'data': 'transaction_data_bus'
}

monitor = GAXIMonitor(
    dut=dut,
    title="CustomMonitor",
    prefix="",
    clock=clock,
    field_config=field_config,
    signal_map=signal_map  # Override automatic discovery
)
```

### Multi-Field Monitoring

```python
# Create field configuration with multiple fields
field_config = FieldConfig()
field_config.add_field(FieldDefinition("addr", 32, format="hex"))
field_config.add_field(FieldDefinition("data", 32, format="hex"))
field_config.add_field(FieldDefinition("cmd", 4, format="hex"))
field_config.add_field(FieldDefinition("id", 8, format="hex"))

# Monitor with multi-signal mode
monitor = GAXIMonitor(
    dut=dut,
    title="MultiFieldMonitor",
    prefix="",
    clock=clock,
    field_config=field_config,
    multi_sig=True  # Individual signals for each field
)
```

## Error Handling

### Signal Resolution Errors
```python
try:
    monitor = GAXIMonitor(dut, "Monitor", "", clock, field_config)
except RuntimeError as e:
    print(f"Signal resolution failed: {e}")
    # Try with manual signal mapping
    signal_map = create_manual_signal_map()
    monitor = GAXIMonitor(dut, "Monitor", "", clock, field_config,
                         signal_map=signal_map)
```

### Monitoring Errors
```python
# Monitor automatically handles signal errors
# Check statistics for error information
stats = monitor.get_stats()
monitor_stats = stats['monitor_stats']
if monitor_stats['x_z_violations'] > 0:
    print(f"X/Z violations detected: {monitor_stats['x_z_violations']}")
```

## Best Practices

### 1. **Choose Appropriate Monitoring Side**
```python
# Monitor master side to see outgoing transactions
master_monitor = GAXIMonitor(..., is_slave=False)

# Monitor slave side to see received transactions  
slave_monitor = GAXIMonitor(..., is_slave=True)
```

### 2. **Match Mode to DUT Implementation**
```python
# For DUT with registered slave interface
monitor = GAXIMonitor(..., is_slave=True, mode='fifo_flop')

# For DUT with combinational interface
monitor = GAXIMonitor(..., is_slave=True, mode='skid')
```

### 3. **Use Callbacks for Real-Time Processing**
```python
# Prefer callbacks over polling
monitor.add_callback(process_transaction)

# Avoid polling the queue directly
# while True:
#     if monitor._recvQ:  # Don't do this
packets = monitor.get_observed_packets()  # Do this instead
```

### 4. **Enable Debug During Development**
```python
monitor = GAXIMonitor(..., super_debug=True)   # Development
monitor = GAXIMonitor(..., super_debug=False)  # Production
```

### 5. **Monitor Statistics for Health**
```python
# Regular statistics checking
stats = monitor.get_stats()
if stats['monitor_stats']['protocol_violations'] > 0:
    print("Protocol violations detected - investigate")
```

The GAXIMonitor provides comprehensive transaction observation capabilities with precise timing control, protocol violation detection, and flexible configuration for thorough verification of GAXI protocol implementations.