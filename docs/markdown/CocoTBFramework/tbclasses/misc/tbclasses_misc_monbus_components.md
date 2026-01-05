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

# monbus_components.py

Monitor Bus Components providing Master and Slave classes for interfacing with any Monitor's consolidated 64-bit event packet bus (monbus). This module offers a generic monitoring interface that can be used with AXI, AHB, APB, or any other bus protocol for comprehensive system-level monitoring and analysis.

## Overview

The `monbus_components.py` module provides specialized GAXI Master and Slave components designed specifically for monitoring bus interfaces. The monitor bus carries structured 64-bit packets containing error, performance, debug, and completion information from various system components.

### Key Features
- **Protocol-agnostic design** works with any bus interface
- **Structured 64-bit packet format** with automatic field extraction
- **Multiple event types** for comprehensive system monitoring
- **Hierarchical addressing** with unit, agent, and channel identification
- **Real-time event processing** and validation
- **Comprehensive statistics** and reporting capabilities
- **Integration with scoreboards** and analysis tools

## Packet Structure

### 64-bit Monitor Bus Packet Format

```
Bits [63:60] - packet_type (4 bits): Event category
Bits [59:56] - event_code  (4 bits): Specific event or error code  
Bits [55:50] - channel_id  (6 bits): Channel and transaction identifier
Bits [49:46] - unit_id     (4 bits): Subsystem identifier
Bits [45:38] - agent_id    (8 bits): Module identifier  
Bits [37:0]  - data        (38 bits): Address, metric value, or payload
```

### Event Classifications

#### MonbusPktType Enumeration

```python
class MonbusPktType(Enum):
    ERROR = 0x0        # Protocol violations, timeouts, errors
    COMPLETION = 0x1   # Transaction completions, milestones
    THRESHOLD = 0x2    # Performance threshold events
    TIMEOUT = 0x3      # Timeout conditions
    PERF = 0x4         # Performance metrics and measurements
    DEBUG = 0xF        # Debug information and diagnostics
```

#### MonbusEventCode Enumeration

```python
class MonbusEventCode(Enum):
    NONE = 0x0           # No specific event
    CMD_TIMEOUT = 0x1    # Command timeout
    DATA_TIMEOUT = 0x2   # Data timeout  
    RESP_TIMEOUT = 0x3   # Response timeout
    RESP_ERROR = 0x4     # Response error
    RESP_SLVERR = 0x5    # Slave error response
    RESP_DECERR = 0x6    # Decode error response
    DATA_ORPHAN = 0x7    # Orphaned data
    RESP_ORPHAN = 0x8    # Orphaned response
    PROTOCOL = 0x9       # Protocol violation
    TRANS_COMPLETE = 0xA # Transaction complete
    ADDR_MISS_T0 = 0xB   # Address miss threshold
```

## Core Classes

### MonbusPacket

Data class representing a structured monitor bus packet with automatic field extraction.

```python
@dataclass
class MonbusPacket:
    raw_data: int                    # Complete 64-bit packet
    packet_type: MonbusPktType       # Event category
    event_code: MonbusEventCode      # Specific event
    channel_id: int                  # Channel identifier (0-63)
    unit_id: int                     # Unit identifier (0-15)  
    agent_id: int                    # Agent identifier (0-255)
    data: int                        # Payload data (38 bits)
    timestamp: float                 # Simulation timestamp
    metadata: Dict[str, Any]         # Additional information
```

#### Class Methods

##### `from_raw_data(raw_data, timestamp=None)`

Create MonbusPacket from 64-bit raw data with automatic field extraction.

**Parameters:**
- `raw_data`: 64-bit integer containing packet data
- `timestamp`: Optional timestamp (uses current sim time if None)

**Returns:** MonbusPacket instance

```python
# Extract packet from raw 64-bit data
raw_packet = 0x1A3C5F7E9B2D4816
packet = MonbusPacket.from_raw_data(raw_packet)

print(f"Type: {packet.packet_type}")
print(f"Event: {packet.event_code}")
print(f"Unit: {packet.unit_id}, Agent: {packet.agent_id}")
print(f"Data: 0x{packet.data:X}")
```

##### `to_raw_data()`

Convert MonbusPacket to 64-bit raw data format.

**Returns:** 64-bit integer representation

```python
# Create packet and convert to raw format
packet = MonbusPacket(
    packet_type=MonbusPktType.ERROR,
    event_code=MonbusEventCode.RESP_TIMEOUT,
    channel_id=5,
    unit_id=2,
    agent_id=10,
    data=0xDEADBEEF
)

raw_data = packet.to_raw_data()
print(f"Raw packet: 0x{raw_data:016X}")
```

### MonbusMaster

GAXI Master specialized for sending monitor bus packets with various event types.

#### Constructor

```python
MonbusMaster(dut, title="MonbusMaster", prefix="", pkt_prefix="monbus",
             unit_id=9, agent_id=99, **kwargs)
```

**Parameters:**
- `dut`: Device Under Test entity
- `title`: Component identifier (default: "MonbusMaster")
- `prefix`: Signal prefix for bus connection (default: "")
- `pkt_prefix`: Packet signal prefix (default: "monbus")
- `unit_id`: Default unit identifier (default: 9)
- `agent_id`: Default agent identifier (default: 99)
- `**kwargs`: Additional GAXI Master parameters

```python
# Create monitor bus master
monitor_master = MonbusMaster(
    dut=dut,
    title="SystemMonitor",
    prefix="mon_",
    unit_id=1,
    agent_id=10
)
```

#### Packet Creation Methods

##### `create_error_packet(event_code, channel_id=0, data=0)`

Create an error event packet.

**Parameters:**
- `event_code`: Error type (MonbusEventCode or integer)
- `channel_id`: Channel identifier (default: 0)
- `data`: Error-specific data (default: 0)

**Returns:** GAXIPacket configured for monitor bus transmission

```python
# Create timeout error packet
error_packet = monitor_master.create_error_packet(
    event_code=MonbusEventCode.CMD_TIMEOUT,
    channel_id=3,
    data=0x1000  # Address that timed out
)

# Send error packet
await monitor_master.send(error_packet)
```

##### `create_completion_packet(event_code=MonbusEventCode.TRANS_COMPLETE, channel_id=0, data=0)`

Create a completion event packet.

**Parameters:**
- `event_code`: Completion type (default: TRANS_COMPLETE)
- `channel_id`: Channel identifier (default: 0)
- `data`: Completion-specific data (default: 0)

**Returns:** GAXIPacket for completion event

```python
# Create transaction completion packet
completion_packet = monitor_master.create_completion_packet(
    event_code=MonbusEventCode.TRANS_COMPLETE,
    channel_id=7,
    data=12345  # Transaction ID
)

await monitor_master.send(completion_packet)
```

##### `create_performance_packet(channel_id=0, data=0)`

Create a performance metrics packet.

**Parameters:**
- `channel_id`: Channel identifier (default: 0)
- `data`: Performance metric value (default: 0)

**Returns:** GAXIPacket for performance data

```python
# Create bandwidth measurement packet
perf_packet = monitor_master.create_performance_packet(
    channel_id=2,
    data=1500000  # Bandwidth in bytes/sec
)

await monitor_master.send(perf_packet)
```

##### `create_debug_packet(channel_id=0, data=0)`

Create a debug information packet.

**Parameters:**
- `channel_id`: Channel identifier (default: 0)  
- `data`: Debug data (default: 0)

**Returns:** GAXIPacket for debug information

```python
# Create debug state packet
debug_packet = monitor_master.create_debug_packet(
    channel_id=1,
    data=0xABCD  # Debug state value
)

await monitor_master.send(debug_packet)
```

##### `create_threshold_packet(channel_id=0, data=0)`

Create a threshold event packet.

**Parameters:**
- `channel_id`: Channel identifier (default: 0)
- `data`: Threshold value or measurement (default: 0)

**Returns:** GAXIPacket for threshold event

```python
# Create latency threshold packet
threshold_packet = monitor_master.create_threshold_packet(
    channel_id=4,
    data=250  # Latency exceeded 250 cycles
)

await monitor_master.send(threshold_packet)
```

##### `create_timeout_packet(event_code=MonbusEventCode.CMD_TIMEOUT, channel_id=0, data=0)`

Create a timeout event packet.

**Parameters:**
- `event_code`: Timeout type (default: CMD_TIMEOUT)
- `channel_id`: Channel identifier (default: 0)
- `data`: Timeout-specific data (default: 0)

**Returns:** GAXIPacket for timeout event

```python
# Create response timeout packet
timeout_packet = monitor_master.create_timeout_packet(
    event_code=MonbusEventCode.RESP_TIMEOUT,
    channel_id=6,
    data=500  # Timeout after 500 cycles
)

await monitor_master.send(timeout_packet)
```

#### Advanced Methods

##### `send_burst_events(events, delay_cycles=1)`

Send multiple events in a burst with configurable delays.

**Parameters:**
- `events`: List of event dictionaries with packet parameters
- `delay_cycles`: Cycles between events (default: 1)

```python
# Send burst of related events
events = [
    {'type': 'error', 'event_code': MonbusEventCode.CMD_TIMEOUT, 'channel_id': 1},
    {'type': 'error', 'event_code': MonbusEventCode.RESP_TIMEOUT, 'channel_id': 1},
    {'type': 'completion', 'event_code': MonbusEventCode.TRANS_COMPLETE, 'channel_id': 1}
]

await monitor_master.send_burst_events(events, delay_cycles=2)
```

### MonbusSlave

GAXI Slave specialized for receiving and processing monitor bus packets with validation and analysis.

#### Constructor

```python
MonbusSlave(dut, title="MonbusSlave", prefix="", pkt_prefix="monbus",
            expected_unit_id=None, expected_agent_id=None, **kwargs)
```

**Parameters:**
- `dut`: Device Under Test entity
- `title`: Component identifier (default: "MonbusSlave")
- `prefix`: Signal prefix for bus connection (default: "")
- `pkt_prefix`: Packet signal prefix (default: "monbus")
- `expected_unit_id`: Expected unit ID for validation (default: None - accept all)
- `expected_agent_id`: Expected agent ID for validation (default: None - accept all)
- `**kwargs`: Additional GAXI Slave parameters

```python
# Create monitor bus slave with validation
monitor_slave = MonbusSlave(
    dut=dut,
    title="EventCollector",
    prefix="mon_",
    expected_unit_id=1,
    expected_agent_id=10
)
```

#### Monitoring and Validation

##### `add_packet_callback(callback)`

Register callback function for received packets.

**Parameters:**
- `callback`: Function accepting MonbusPacket parameter

```python
def process_error_events(packet):
    if packet.packet_type == MonbusPktType.ERROR:
        print(f"Error detected: {packet.event_code} on channel {packet.channel_id}")

monitor_slave.add_packet_callback(process_error_events)
```

##### `start_monitoring()`

Start monitoring for incoming packets (non-blocking).

```python
# Start packet monitoring
await monitor_slave.start_monitoring()

# Monitoring runs in background
await run_test_sequence()
```

##### `get_statistics()`

Get comprehensive monitoring statistics.

**Returns:** Dictionary with packet statistics and analysis

```python
stats = monitor_slave.get_statistics()
print(f"Total packets: {stats['packets_received']}")
print(f"Error packets: {stats['error_packets']}")
print(f"Performance packets: {stats['performance_packets']}")
print(f"Verification errors: {stats['verification_errors']}")
```

##### `generate_report()`

Generate comprehensive monitoring report with packet analysis.

**Returns:** Formatted string report

```python
report = monitor_slave.generate_report()
print(report)

# Example output:
# MonbusSlave Monitor Report
# ================================================
# Total Packets Received: 150
# Monitoring Duration: 2500.0 ns
# 
# Packet Type Breakdown:
#   Error Packets: 25
#   Completion Packets: 100
#   Timeout Packets: 10
#   Performance Packets: 15
#   Debug Packets: 0
#   Unknown Packets: 0
# 
# ✅ No verification errors detected
```

##### `reset_statistics()`

Reset all statistics and packet history.

```python
# Reset for new test phase
monitor_slave.reset_statistics()
```

## Utility Functions

### `create_monbus_master(dut, unit_id=9, agent_id=99, **kwargs)`

Utility function for creating monitor bus master with default settings.

**Parameters:**
- `dut`: Device Under Test entity
- `unit_id`: Unit identifier (default: 9)
- `agent_id`: Agent identifier (default: 99)
- `**kwargs`: Additional parameters

**Returns:** Configured MonbusMaster instance

```python
# Quick master creation
master = create_monbus_master(dut, unit_id=2, agent_id=15)
```

### `create_monbus_slave(dut, expected_unit_id=None, expected_agent_id=None, **kwargs)`

Utility function for creating monitor bus slave with default settings.

**Parameters:**
- `dut`: Device Under Test entity
- `expected_unit_id`: Expected unit ID for validation (default: None)
- `expected_agent_id`: Expected agent ID for validation (default: None)
- `**kwargs`: Additional parameters

**Returns:** Configured MonbusSlave instance

```python
# Quick slave creation with validation
slave = create_monbus_slave(dut, expected_unit_id=2, expected_agent_id=15)
```

## Usage Patterns

### Basic Monitor Bus Setup

```python
import cocotb
from cocotb.triggers import Timer
from CocoTBFramework.tbclasses.misc.monbus_components import (
    create_monbus_master, create_monbus_slave,
    MonbusPktType, MonbusEventCode
)

@cocotb.test()
async def basic_monitor_test(dut):
    """Basic monitor bus communication test"""
    
    # Create components
    master = create_monbus_master(dut, unit_id=1, agent_id=10)
    slave = create_monbus_slave(dut, expected_unit_id=1, expected_agent_id=10)
    
    # Start monitoring
    await slave.start_monitoring()
    
    # Send various event types
    await master.send(master.create_error_packet(
        MonbusEventCode.CMD_TIMEOUT, channel_id=5, data=0x1000
    ))
    
    await master.send(master.create_completion_packet(
        channel_id=5, data=12345
    ))
    
    await master.send(master.create_performance_packet(
        channel_id=1, data=1500000
    ))
    
    # Wait for processing
    await Timer(100, units='ns')
    
    # Check results
    stats = slave.get_statistics()
    assert stats['packets_received'] == 3
    assert stats['error_packets'] == 1
    assert stats['completion_packets'] == 1
    assert stats['performance_packets'] == 1
```

### Advanced Event Processing

```python
@cocotb.test()
async def advanced_monitoring_test(dut):
    """Advanced monitoring with event processing and analysis"""
    
    master = create_monbus_master(dut, unit_id=2, agent_id=20)
    slave = create_monbus_slave(dut, expected_unit_id=2, expected_agent_id=20)
    
    # Event tracking
    error_events = []
    performance_data = []
    
    def error_tracker(packet):
        if packet.packet_type == MonbusPktType.ERROR:
            error_events.append({
                'event': packet.event_code,
                'channel': packet.channel_id,
                'data': packet.data,
                'timestamp': packet.timestamp
            })
    
    def performance_tracker(packet):
        if packet.packet_type == MonbusPktType.PERF:
            performance_data.append({
                'channel': packet.channel_id,
                'value': packet.data,
                'timestamp': packet.timestamp
            })
    
    # Register callbacks
    slave.add_packet_callback(error_tracker)
    slave.add_packet_callback(performance_tracker)
    
    # Start monitoring
    await slave.start_monitoring()
    
    # Simulate complex scenario
    for cycle in range(100):
        # Send performance data every 10 cycles
        if cycle % 10 == 0:
            await master.send(master.create_performance_packet(
                channel_id=1, data=cycle * 1000
            ))
        
        # Simulate errors occasionally
        if cycle % 25 == 0:
            await master.send(master.create_error_packet(
                MonbusEventCode.RESP_TIMEOUT,
                channel_id=cycle % 8,
                data=cycle
            ))
        
        await Timer(10, units='ns')
    
    # Analysis
    print(f"Captured {len(error_events)} errors")
    print(f"Captured {len(performance_data)} performance samples")
    
    # Generate comprehensive report
    report = slave.generate_report()
    print(report)
```

### Cross-Protocol Integration

```python
@cocotb.test()
async def cross_protocol_monitoring(dut):
    """Monitor multiple protocols using unified monitor bus"""
    
    # Create multiple monitor masters for different protocols
    axi_monitor = create_monbus_master(dut, unit_id=1, agent_id=1)  # AXI
    apb_monitor = create_monbus_master(dut, unit_id=2, agent_id=2)  # APB
    fifo_monitor = create_monbus_master(dut, unit_id=3, agent_id=3) # FIFO
    
    # Central event collector
    event_collector = create_monbus_slave(dut)
    
    # Protocol-specific event tracking
    protocol_stats = {1: {'name': 'AXI', 'events': 0},
                     2: {'name': 'APB', 'events': 0},
                     3: {'name': 'FIFO', 'events': 0}}
    
    def protocol_event_tracker(packet):
        unit_id = packet.unit_id
        if unit_id in protocol_stats:
            protocol_stats[unit_id]['events'] += 1
            print(f"{protocol_stats[unit_id]['name']} event: "
                  f"{packet.event_code} on channel {packet.channel_id}")
    
    event_collector.add_packet_callback(protocol_event_tracker)
    await event_collector.start_monitoring()
    
    # Simulate events from different protocols
    test_scenarios = [
        (axi_monitor, MonbusEventCode.RESP_SLVERR, 1),
        (apb_monitor, MonbusEventCode.CMD_TIMEOUT, 2),
        (fifo_monitor, MonbusEventCode.DATA_ORPHAN, 3),
        (axi_monitor, MonbusEventCode.TRANS_COMPLETE, 1),
        (apb_monitor, MonbusEventCode.TRANS_COMPLETE, 2),
    ]
    
    for monitor, event_code, channel in test_scenarios:
        if event_code in [MonbusEventCode.RESP_SLVERR, MonbusEventCode.CMD_TIMEOUT, MonbusEventCode.DATA_ORPHAN]:
            packet = monitor.create_error_packet(event_code, channel, 0x5555)
        else:
            packet = monitor.create_completion_packet(event_code, channel, 0xAAAA)
        
        await monitor.send(packet)
        await Timer(20, units='ns')
    
    # Final analysis
    for unit_id, stats in protocol_stats.items():
        print(f"{stats['name']}: {stats['events']} events")
```

### System-Level Monitoring

```python
class SystemMonitor:
    """Comprehensive system monitoring using monitor bus"""
    
    def __init__(self, dut):
        self.dut = dut
        self.masters = {}
        self.slave = create_monbus_slave(dut)
        self.event_history = []
        self.error_count = 0
        self.performance_metrics = {}
        
    def add_protocol_monitor(self, protocol_name, unit_id, agent_id):
        """Add a protocol-specific monitor master"""
        master = create_monbus_master(self.dut, unit_id=unit_id, agent_id=agent_id)
        self.masters[protocol_name] = master
        return master
    
    async def start_system_monitoring(self):
        """Initialize system-wide monitoring"""
        def event_processor(packet):
            self.event_history.append(packet)
            
            if packet.packet_type == MonbusPktType.ERROR:
                self.error_count += 1
                print(f"SYSTEM ERROR: {packet.event_code} from unit {packet.unit_id}")
            
            elif packet.packet_type == MonbusPktType.PERF:
                channel = packet.channel_id
                if channel not in self.performance_metrics:
                    self.performance_metrics[channel] = []
                self.performance_metrics[channel].append(packet.data)
        
        self.slave.add_packet_callback(event_processor)
        await self.slave.start_monitoring()
    
    async def report_error(self, protocol, error_type, channel, data=0):
        """Report error from specific protocol"""
        if protocol in self.masters:
            packet = self.masters[protocol].create_error_packet(error_type, channel, data)
            await self.masters[protocol].send(packet)
    
    async def report_performance(self, protocol, channel, metric_value):
        """Report performance metric from specific protocol"""
        if protocol in self.masters:
            packet = self.masters[protocol].create_performance_packet(channel, metric_value)
            await self.masters[protocol].send(packet)
    
    def get_system_status(self):
        """Get comprehensive system status"""
        return {
            'total_events': len(self.event_history),
            'error_count': self.error_count,
            'performance_channels': len(self.performance_metrics),
            'monitored_protocols': list(self.masters.keys())
        }

# Usage
@cocotb.test()
async def system_level_test(dut):
    monitor = SystemMonitor(dut)
    
    # Add protocol monitors
    monitor.add_protocol_monitor("AXI4", unit_id=1, agent_id=1)
    monitor.add_protocol_monitor("APB", unit_id=2, agent_id=2)
    monitor.add_protocol_monitor("FIFO", unit_id=3, agent_id=3)
    
    # Start monitoring
    await monitor.start_system_monitoring()
    
    # Simulate system operation
    await monitor.report_error("AXI4", MonbusEventCode.RESP_SLVERR, 1, 0x1000)
    await monitor.report_performance("AXI4", 1, 150000)
    await monitor.report_error("APB", MonbusEventCode.CMD_TIMEOUT, 2, 0x2000)
    
    # Check system status
    status = monitor.get_system_status()
    print(f"System events: {status['total_events']}")
    print(f"System errors: {status['error_count']}")
```

## Best Practices

### Event Design
- **Use meaningful event codes** that clearly identify the condition
- **Include relevant data** in the 38-bit payload (addresses, values, IDs)
- **Use hierarchical addressing** (unit_id, agent_id, channel_id) for organization
- **Document event meanings** and expected response actions

### Integration Strategy
- **Start with basic monitoring** and gradually add sophistication
- **Use callbacks** for real-time event processing
- **Implement validation** with expected unit/agent IDs when appropriate
- **Generate regular reports** for trend analysis and debugging

### Performance Considerations
- **Monitor buffer usage** for high-frequency events
- **Use burst sending** for related events to improve efficiency
- **Configure appropriate validation** to filter irrelevant events
- **Archive event history** periodically for long-running tests

### System Architecture
- **Define clear unit/agent ID schemes** for different subsystems
- **Establish event code conventions** across protocols
- **Implement centralized event collection** for system-level analysis
- **Use monitor bus for cross-protocol coordination** and verification

The monitor bus system provides a powerful and flexible foundation for comprehensive system monitoring, enabling unified event collection and analysis across multiple protocols and verification components.