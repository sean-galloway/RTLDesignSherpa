# packet_factory.py

Generic packet factory that works across all protocols (GAXI, FIFO, APB, etc.) providing comprehensive packet creation, management, and processing capabilities. This module eliminates the need for packet_class parameters and provides better abstraction for verification environments.

## Overview

The `packet_factory.py` module provides a complete packet handling ecosystem with factories, transaction handlers, field unpackers, and convenience functions. It's designed to work seamlessly across different protocols while providing consistent interfaces and comprehensive error handling.

## Core Classes

### PacketFactory

Generic factory for creating and managing packets across any protocol.

#### Constructor

```python
PacketFactory(packet_class: Type[Packet], field_config: FieldConfig)
```

**Parameters:**
- `packet_class`: Class to use for packet creation (must be a subclass of Packet)
- `field_config`: Field configuration for packets

**Raises:**
- `TypeError`: If packet_class is not a subclass of Packet

```python
from .packet import Packet
from .field_config import FieldConfig

# Create field configuration
config = FieldConfig()
config.add_field(FieldDefinition("addr", 32, format="hex"))
config.add_field(FieldDefinition("data", 32, format="hex"))

# Create packet factory
factory = PacketFactory(Packet, config)
```

#### Methods

##### `create_packet(**kwargs) -> Packet`

Create a new packet with the configured class and field config.

**Parameters:**
- `**kwargs`: Initial field values

**Returns:** New packet instance

```python
# Create packet with initial values
packet = factory.create_packet(addr=0x1000, data=0xDEADBEEF)

# Create empty packet
empty_packet = factory.create_packet()
```

##### `create_timed_packet(start_time: Optional[float] = None, **kwargs) -> Packet`

Create a packet with timing information.

**Parameters:**
- `start_time`: Start time in simulation time units
- `**kwargs`: Initial field values

**Returns:** New packet with start_time set

```python
import cocotb

# Create packet with current simulation time
timed_packet = factory.create_timed_packet(
    start_time=cocotb.utils.get_sim_time(),
    addr=0x2000,
    data=0x12345678
)
```

##### `finish_packet(packet: Packet, end_time: Optional[float] = None, data_dict: Optional[Dict[str, Any]] = None) -> Packet`

Complete a packet with data and timing information.

**Parameters:**
- `packet`: Packet to complete
- `end_time`: End time in simulation time units
- `data_dict`: Field data to unpack into packet

**Returns:** The completed packet (for chaining)

```python
# Complete packet with end time and data
completed_packet = factory.finish_packet(
    packet,
    end_time=cocotb.utils.get_sim_time(),
    data_dict={'addr': 0x3000, 'data': 0xCAFEBABE}
)
```

##### `create_from_data(data_dict: Dict[str, Any], start_time: Optional[float] = None, end_time: Optional[float] = None) -> Packet`

Create a packet directly from field data.

**Parameters:**
- `data_dict`: Field values
- `start_time`: Optional start time
- `end_time`: Optional end time

**Returns:** New packet with data and timing

```python
# Create packet from captured data
data = {'addr': 0x4000, 'data': 0xDEADBEEF}
packet = factory.create_from_data(
    data_dict=data,
    start_time=1000,
    end_time=2000
)
```

##### `create_random_packet(randomizer=None, **fixed_fields) -> Packet`

Create a packet with random field values.

**Parameters:**
- `randomizer`: Optional randomizer to use for field values
- `**fixed_fields`: Fields with fixed values (override random)

**Returns:** New packet with random/fixed field values

```python
# Create random packet with fixed address
random_packet = factory.create_random_packet(
    randomizer=my_randomizer,
    addr=0x1000  # Fixed address, randomize other fields
)
```

##### `copy_packet(source_packet: Packet, **overrides) -> Packet`

Create a copy of an existing packet with optional field overrides.

**Parameters:**
- `source_packet`: Packet to copy
- `**overrides`: Fields to override in the copy

**Returns:** New packet that's a copy of the source

```python
# Copy packet with modified data
original = factory.create_packet(addr=0x1000, data=0xDEADBEEF)
modified = factory.copy_packet(original, data=0x12345678)
```

##### `validate_packet(packet: Packet) -> bool`

Validate that a packet has all required fields set.

**Parameters:**
- `packet`: Packet to validate

**Returns:** True if packet is valid, False otherwise

```python
if factory.validate_packet(packet):
    process_packet(packet)
else:
    log.error("Packet validation failed")
```

### TransactionHandler

Generic handler for transaction processing across any protocol that encapsulates common transaction patterns.

#### Constructor

```python
TransactionHandler(packet_factory: PacketFactory, callbacks: List[Callable], log, component_name: str)
```

**Parameters:**
- `packet_factory`: Factory for creating packets
- `callbacks`: List of callback functions
- `log`: Logger instance
- `component_name`: Name for logging

```python
# Create transaction handler
callbacks = [scoreboard.record_transaction, monitor.log_transaction]
handler = TransactionHandler(factory, callbacks, log, "TestMaster")
```

#### Methods

##### `create_transaction(start_time: float, **initial_fields) -> Packet`

Create a new transaction packet with start time and initial fields.

**Parameters:**
- `start_time`: Transaction start time
- `**initial_fields`: Initial field values

**Returns:** New transaction packet

```python
# Create transaction
transaction = handler.create_transaction(
    start_time=cocotb.utils.get_sim_time(),
    addr=0x1000,
    cmd=0x2  # WRITE
)
```

##### `finish_transaction(packet: Packet, end_time: float, data_dict: Optional[Dict[str, Any]] = None, validate: bool = True) -> Packet`

Complete a transaction and trigger callbacks.

**Parameters:**
- `packet`: Packet to complete
- `end_time`: Transaction end time
- `data_dict`: Optional field data
- `validate`: Whether to validate packet before callbacks

**Returns:** Completed packet

```python
# Complete transaction
completed = handler.finish_transaction(
    packet=transaction,
    end_time=cocotb.utils.get_sim_time(),
    data_dict={'data': 0xDEADBEEF},
    validate=True
)
```

##### `add_callback(callback: Callable)`

Add a new callback function.

```python
handler.add_callback(new_monitor.log_transaction)
```

##### `remove_callback(callback: Callable)`

Remove a callback function.

```python
handler.remove_callback(old_monitor.log_transaction)
```

##### `get_stats() -> Dict[str, Any]`

Get transaction processing statistics.

**Returns:** Dictionary with processing statistics

```python
stats = handler.get_stats()
print(f"Transactions processed: {stats['transactions_processed']}")
print(f"Validation failures: {stats['validation_failures']}")
print(f"Callback errors: {stats['callback_errors']}")
```

### FieldUnpacker

Generic helper for unpacking combined field values into individual fields.

#### Constructor

```python
FieldUnpacker(field_config: FieldConfig, log, component_name: str)
```

**Parameters:**
- `field_config`: Field configuration
- `log`: Logger instance
- `component_name`: Component name for logging

```python
unpacker = FieldUnpacker(field_config, log, "DataUnpacker")
```

#### Methods

##### `unpack_combined_fields(combined_value: int) -> Dict[str, int]`

Unpack a combined value into individual fields.

**Parameters:**
- `combined_value`: Combined integer value containing all fields

**Returns:** Dictionary of field_name -> field_value mappings

```python
# Unpack combined 32-bit value into fields
combined = 0x12345678
fields = unpacker.unpack_combined_fields(combined)
print(fields)  # {'field1': value1, 'field2': value2, ...}
```

## Convenience Functions

### `create_packet_system()`

Create a complete packet handling system for any protocol component.

```python
create_packet_system(packet_class: Type[Packet], field_config: FieldConfig, 
                     log, component_name: str, callbacks: Optional[List[Callable]] = None)
```

**Parameters:**
- `packet_class`: Packet class to use
- `field_config`: Field configuration
- `log`: Logger
- `component_name`: Component name for logging
- `callbacks`: Optional initial callback functions

**Returns:** Tuple of (PacketFactory, TransactionHandler, FieldUnpacker)

```python
# Create complete packet system
factory, handler, unpacker = create_packet_system(
    Packet, field_config, log, "TestComponent", [callback1, callback2]
)
```

### `create_monitor_system()`

Create a packet system optimized for monitors.

```python
create_monitor_system(packet_class: Type[Packet], field_config: FieldConfig,
                     log, component_name: str, callbacks: Optional[List[Callable]] = None)
```

**Returns:** Tuple of (PacketFactory, TransactionHandler, FieldUnpacker)

```python
# Create monitor packet system
factory, handler, unpacker = create_monitor_system(
    Packet, field_config, log, "ProtocolMonitor", [monitor_callback]
)
```

### `create_master_system()`

Create a packet system optimized for masters.

```python
create_master_system(packet_class: Type[Packet], field_config: FieldConfig,
                    log, component_name: str)
```

**Returns:** PacketFactory instance (masters typically don't need full TransactionHandler)

```python
# Create master packet system
factory = create_master_system(Packet, field_config, log, "TestMaster")
```

### `create_slave_system()`

Create a packet system optimized for slaves.

```python
create_slave_system(packet_class: Type[Packet], field_config: FieldConfig,
                   log, component_name: str, callbacks: Optional[List[Callable]] = None)
```

**Returns:** Tuple of (PacketFactory, TransactionHandler, FieldUnpacker)

```python
# Create slave packet system
factory, handler, unpacker = create_slave_system(
    Packet, field_config, log, "TestSlave", [response_callback]
)
```

## Usage Patterns

### Basic Factory Usage

```python
# Set up packet factory
config = FieldConfig()
config.add_field(FieldDefinition("addr", 32))
config.add_field(FieldDefinition("data", 32))
config.add_field(FieldDefinition("cmd", 4))

factory = PacketFactory(Packet, config)

# Create packets
write_packet = factory.create_packet(addr=0x1000, data=0xDEADBEEF, cmd=0x2)
read_packet = factory.create_packet(addr=0x2000, cmd=0x1)

# Create timed packet
timed_packet = factory.create_timed_packet(
    start_time=cocotb.utils.get_sim_time(),
    addr=0x3000,
    data=0x12345678
)

# Complete transaction
completed = factory.finish_packet(
    timed_packet,
    end_time=cocotb.utils.get_sim_time(),
    data_dict={'status': 0x0}  # Add status field
)
```

### Master Component Usage

```python
class TestMaster:
    def __init__(self, dut, field_config):
        self.dut = dut
        self.factory = create_master_system(Packet, field_config, log, "TestMaster")
        self.pending_transactions = {}
    
    @cocotb.coroutine
    def write_transaction(self, addr, data):
        """Perform write transaction"""
        # Create write packet
        packet = self.factory.create_timed_packet(
            start_time=cocotb.utils.get_sim_time(),
            addr=addr,
            data=data,
            cmd=0x2  # WRITE
        )
        
        # Drive to DUT
        yield self.drive_packet(packet)
        
        # Wait for completion
        yield self.wait_for_response(packet)
        
        # Complete packet
        completed_packet = self.factory.finish_packet(
            packet,
            end_time=cocotb.utils.get_sim_time()
        )
        
        return completed_packet
    
    @cocotb.coroutine
    def drive_packet(self, packet):
        """Drive packet to DUT"""
        fifo_data = packet.pack_for_fifo()
        
        # Drive signals
        for field_name, value in fifo_data.items():
            signal = getattr(self.dut, f"{field_name}_i")
            signal.value = value
        
        self.dut.valid_i.value = 1
        yield RisingEdge(self.dut.clk)
        self.dut.valid_i.value = 0
    
    @cocotb.coroutine
    def wait_for_response(self, packet):
        """Wait for response from DUT"""
        yield RisingEdge(self.dut.response_valid_o)
        # Handle response...
```

### Monitor Component Usage

```python
class ProtocolMonitor:
    def __init__(self, dut, field_config):
        self.dut = dut
        
        # Set up packet system with callbacks
        callbacks = [self.log_transaction, self.forward_to_scoreboard]
        self.factory, self.handler, self.unpacker = create_monitor_system(
            Packet, field_config, log, "ProtocolMonitor", callbacks
        )
        
        self.observed_packets = []
    
    @cocotb.coroutine
    def monitor_transactions(self):
        """Monitor protocol transactions"""
        while True:
            yield RisingEdge(self.dut.clk)
            
            # Check for valid transaction
            if self.dut.valid.value == 1 and self.dut.ready.value == 1:
                # Capture transaction start
                start_time = cocotb.utils.get_sim_time()
                transaction = self.handler.create_transaction(start_time)
                
                # Capture field data
                captured_data = {}
                for field_name in self.factory.field_config.field_names():
                    signal = getattr(self.dut, f"{field_name}")
                    captured_data[field_name] = int(signal.value)
                
                # Complete transaction (triggers callbacks)
                completed = self.handler.finish_transaction(
                    transaction,
                    end_time=cocotb.utils.get_sim_time(),
                    data_dict=captured_data
                )
                
                self.observed_packets.append(completed)
    
    def log_transaction(self, packet):
        """Callback: Log observed transaction"""
        log.info(f"Observed: {packet.formatted(compact=True)}")
    
    def forward_to_scoreboard(self, packet):
        """Callback: Forward to scoreboard"""
        self.scoreboard.add_observed_transaction(packet)
```

### Slave Component Usage

```python
class TestSlave:
    def __init__(self, dut, field_config):
        self.dut = dut
        
        # Set up packet system
        callbacks = [self.update_statistics]
        self.factory, self.handler, self.unpacker = create_slave_system(
            Packet, field_config, log, "TestSlave", callbacks
        )
        
        self.memory = {}
    
    @cocotb.coroutine
    def handle_requests(self):
        """Handle incoming requests"""
        while True:
            yield RisingEdge(self.dut.clk)
            
            # Check for incoming request
            if self.dut.request_valid.value == 1:
                # Create transaction
                start_time = cocotb.utils.get_sim_time()
                request = self.handler.create_transaction(start_time)
                
                # Capture request data
                request_data = {}
                for field_name in self.factory.field_config.field_names():
                    signal = getattr(self.dut, f"req_{field_name}")
                    request_data[field_name] = int(signal.value)
                
                # Process request
                response_data = yield self.process_request(request_data)
                
                # Complete transaction
                completed = self.handler.finish_transaction(
                    request,
                    end_time=cocotb.utils.get_sim_time(),
                    data_dict=response_data
                )
                
                # Send response
                yield self.send_response(completed)
    
    @cocotb.coroutine
    def process_request(self, request_data):
        """Process incoming request"""
        addr = request_data['addr']
        cmd = request_data['cmd']
        
        if cmd == 0x1:  # READ
            data = self.memory.get(addr, 0)
            return {'data': data, 'status': 0}  # OK
        
        elif cmd == 0x2:  # WRITE
            self.memory[addr] = request_data['data']
            return {'status': 0}  # OK
        
        else:
            return {'status': 1}  # ERROR
    
    @cocotb.coroutine
    def send_response(self, response_packet):
        """Send response to master"""
        fifo_data = response_packet.pack_for_fifo()
        
        # Drive response signals
        for field_name, value in fifo_data.items():
            signal = getattr(self.dut, f"resp_{field_name}")
            signal.value = value
        
        self.dut.response_valid.value = 1
        yield RisingEdge(self.dut.clk)
        self.dut.response_valid.value = 0
    
    def update_statistics(self, packet):
        """Callback: Update slave statistics"""
        self.stats.record_transaction_processed()
```

### Advanced Transaction Handling

```python
class AdvancedTransactionProcessor:
    def __init__(self, field_config):
        # Create packet system
        self.factory, self.handler, self.unpacker = create_packet_system(
            Packet, field_config, log, "AdvancedProcessor"
        )
        
        # Add specialized callbacks
        self.handler.add_callback(self.validate_protocol_rules)
        self.handler.add_callback(self.update_performance_metrics)
        self.handler.add_callback(self.check_security_constraints)
        
        self.protocol_violations = 0
        self.performance_data = []
        self.security_alerts = []
    
    def validate_protocol_rules(self, packet):
        """Callback: Validate protocol-specific rules"""
        # Check address alignment
        if packet.addr % 4 != 0:
            self.protocol_violations += 1
            log.warning(f"Unaligned address: 0x{packet.addr:X}")
        
        # Check command validity
        valid_commands = [0x0, 0x1, 0x2, 0x3]
        if packet.cmd not in valid_commands:
            self.protocol_violations += 1
            log.error(f"Invalid command: {packet.cmd}")
    
    def update_performance_metrics(self, packet):
        """Callback: Update performance metrics"""
        if packet.start_time and packet.end_time:
            duration = packet.end_time - packet.start_time
            self.performance_data.append({
                'duration': duration,
                'timestamp': packet.end_time,
                'transaction_type': packet.cmd
            })
            
            # Keep only recent data
            if len(self.performance_data) > 1000:
                self.performance_data = self.performance_data[-500:]
    
    def check_security_constraints(self, packet):
        """Callback: Check security constraints"""
        # Check for suspicious address patterns
        if packet.addr >= 0xF000:  # Privileged region
            self.security_alerts.append({
                'type': 'privileged_access',
                'addr': packet.addr,
                'timestamp': packet.end_time
            })
            log.warning(f"Access to privileged region: 0x{packet.addr:X}")
    
    def get_analysis_report(self):
        """Generate comprehensive analysis report"""
        avg_duration = 0
        if self.performance_data:
            avg_duration = sum(p['duration'] for p in self.performance_data) / len(self.performance_data)
        
        return {
            'transactions_processed': len(self.performance_data),
            'protocol_violations': self.protocol_violations,
            'security_alerts': len(self.security_alerts),
            'average_duration': avg_duration,
            'recent_alerts': self.security_alerts[-5:]  # Last 5 alerts
        }
```

### Field Unpacking Usage

```python
class CombinedSignalProcessor:
    def __init__(self, field_config):
        self.unpacker = FieldUnpacker(field_config, log, "SignalProcessor")
        self.factory = PacketFactory(Packet, field_config)
    
    def process_combined_signal(self, combined_value):
        """Process a combined signal value"""
        # Unpack combined value into individual fields
        field_values = self.unpacker.unpack_combined_fields(combined_value)
        
        # Create packet from unpacked fields
        packet = self.factory.create_from_data(field_values)
        
        # Validate and process
        if self.factory.validate_packet(packet):
            return self.process_valid_packet(packet)
        else:
            log.error("Invalid packet after unpacking")
            return None
    
    def process_valid_packet(self, packet):
        """Process a validated packet"""
        # Protocol-specific processing
        return packet
```

### Random Packet Generation

```python
class RandomPacketGenerator:
    def __init__(self, field_config, randomizer):
        self.factory = PacketFactory(Packet, field_config)
        self.randomizer = randomizer
    
    def generate_test_sequence(self, count=100):
        """Generate random test packet sequence"""
        packets = []
        
        for i in range(count):
            # Generate random packet
            packet = self.factory.create_random_packet(
                randomizer=self.randomizer,
                # Fix some fields for test consistency
                cmd=0x2 if i % 2 == 0 else 0x1  # Alternate READ/WRITE
            )
            
            packets.append(packet)
        
        return packets
    
    def generate_burst_sequence(self, base_addr, burst_length):
        """Generate burst transaction sequence"""
        packets = []
        
        for i in range(burst_length):
            packet = self.factory.create_packet(
                addr=base_addr + i*4,
                data=self.randomizer.next()['data'] if hasattr(self.randomizer, 'next') else i*0x100,
                cmd=0x2  # WRITE
            )
            packets.append(packet)
        
        return packets
```

## Error Handling

The packet factory system includes comprehensive error handling:

### Validation Errors
```python
try:
    packet = factory.create_packet(addr="invalid")  # Wrong type
except ValueError as e:
    log.error(f"Packet creation failed: {e}")

# Use validation
if not factory.validate_packet(packet):
    log.error("Packet validation failed")
    # Handle invalid packet
```

### Callback Errors
```python
def problematic_callback(packet):
    raise Exception("Callback failed")

handler.add_callback(problematic_callback)

# Errors are caught and logged, other callbacks continue
completed = handler.finish_transaction(packet, end_time)
stats = handler.get_stats()
print(f"Callback errors: {stats['callback_errors']}")
```

## Best Practices

### 1. **Use Appropriate Factory Functions**
```python
# For masters - simple packet creation
master_factory = create_master_system(Packet, config, log, "Master")

# For monitors - full transaction handling with callbacks
monitor_factory, monitor_handler, _ = create_monitor_system(
    Packet, config, log, "Monitor", [callback1, callback2]
)
```

### 2. **Validate Packets Before Processing**
```python
if factory.validate_packet(packet):
    process_packet(packet)
else:
    handle_invalid_packet(packet)
```

### 3. **Use Callbacks for Modular Processing**
```python
# Separate concerns with different callbacks
handler.add_callback(scoreboard.record_transaction)    # Verification
handler.add_callback(performance_monitor.update)       # Performance
handler.add_callback(security_checker.validate)        # Security
```

### 4. **Handle Timing Information**
```python
# Always use timed packets for performance analysis
packet = factory.create_timed_packet(start_time=cocotb.utils.get_sim_time())
# ... process transaction ...
completed = factory.finish_packet(packet, end_time=cocotb.utils.get_sim_time())
```

### 5. **Monitor Statistics**
```python
# Regular statistics monitoring
def check_handler_health():
    stats = handler.get_stats()
    if stats['validation_failures'] > 10:
        log.warning("High validation failure rate")
    if stats['callback_errors'] > 0:
        log.error("Callback errors detected")
```

The packet factory system provides a comprehensive, protocol-agnostic foundation for packet handling in verification environments, with robust error handling, flexible callback systems, and optimized performance.
