# gaxi_monitor_base.py

Base class providing common GAXI monitoring functionality using unified infrastructure. Eliminates duplication while preserving exact APIs and timing-critical behavior.

## Overview

The `GAXIMonitorBase` class provides:
- **Common monitoring functionality** shared by GAXIMonitor and GAXISlave
- **Signal resolution and data collection** setup from GAXIComponentBase
- **Unified field configuration** handling and packet management
- **Memory model integration** using base MemoryModel directly
- **Clean data collection** with automatic field unpacking
- **Unified packet finishing** without conditional complexity

This base class eliminates code duplication between monitor components while preserving exact timing-critical behavior.

## Class

### GAXIMonitorBase

```python
class GAXIMonitorBase(GAXIComponentBase, BusMonitor):
    def __init__(self, dut, title, prefix, clock, field_config,
                 bus_name='', pkt_prefix='', multi_sig=False,
                 protocol_type=None,  # Set by subclass
                 log=None, super_debug=False, signal_map=None, **kwargs)
```

**Parameters:**
- `dut`: Device under test
- `title`: Component title/name
- `prefix`: Bus prefix
- `clock`: Clock signal
- `field_config`: Field configuration
- `mode`: GAXI mode ('skid', 'fifo_mux', 'fifo_flop')
- `bus_name`: Bus/channel name
- `pkt_prefix`: Packet field prefix
- `multi_sig`: Whether using multi-signal mode
- `protocol_type`: Must be set by subclass ('gaxi_master' or 'gaxi_slave')
- `log`: Logger instance
- `super_debug`: Enable detailed debugging
- `signal_map`: Optional manual signal mapping override
- `**kwargs`: Additional arguments for BusMonitor

## Core Methods

### Data Collection

#### `_get_data_dict()`
Clean data collection with automatic field unpacking.

This replaces messy conditional unpacking logic that was duplicated in both GAXIMonitor and GAXISlave. Uses the unified DataCollectionStrategy.collect_and_unpack_data() method.

**Returns:** Dictionary of field values, properly unpacked

```python
# Internal method used by subclasses
data_dict = self._get_data_dict()
# Returns: {'addr': 0x1000, 'data': 0xDEADBEEF, 'cmd': 0x2}
```

#### `_finish_packet(current_time, packet, data_dict=None)`
Clean packet finishing without conditional complexity.

Replaces duplicate _finish_packet logic that was in both GAXIMonitor and GAXISlave with identical functionality.

**Parameters:**
- `current_time`: Current simulation time
- `packet`: Packet to finish
- `data_dict`: Optional field data (if None, will collect fresh data)

```python
# Internal method used by subclasses
packet = GAXIPacket(self.field_config)
packet.start_time = current_time
data_dict = self._get_data_dict()
self._finish_packet(current_time, packet, data_dict)
```

### Packet Management

#### `create_packet(**field_values)`
Create a packet with specified field values.

**Parameters:**
- `**field_values`: Initial field values

**Returns:** GAXIPacket instance with specified field values

```python
# Create packet with initial values
packet = monitor.create_packet(addr=0x1000, data=0xDEADBEEF)
```

#### `get_observed_packets(count=None)`
Get observed packets from standard cocotb _recvQ.

**Parameters:**
- `count`: Number of packets to return (None = all)

**Returns:** List of observed packets

```python
# Get all observed packets
all_packets = monitor.get_observed_packets()

# Get last 10 packets
recent_packets = monitor.get_observed_packets(10)
```

#### `clear_queue()`
Clear the observed transactions queue using standard cocotb pattern.

```python
monitor.clear_queue()
```

### Memory Operations

#### `handle_memory_write(packet)`
Handle memory write using unified memory integration.

**Parameters:**
- `packet`: Packet to write to memory

**Returns:** Success boolean

```python
success = monitor.handle_memory_write(packet)
if success:
    log.debug("Memory write successful")
```

#### `handle_memory_read(packet)`
Handle memory read using unified memory integration.

**Parameters:**
- `packet`: Packet with address to read

**Returns:** Tuple of (success, data)

```python
success, data = monitor.handle_memory_read(packet)
if success:
    log.debug(f"Memory read successful, data=0x{data:X}")
```

### Statistics

#### `get_base_stats()`
Get base statistics common to all GAXI monitoring components.

Subclasses should call this and add their own specific statistics.

**Returns:** Dictionary containing base statistics

```python
base_stats = monitor.get_base_stats()
print(f"Monitor stats: {base_stats['monitor_stats']}")
print(f"Observed packets: {base_stats['observed_packets']}")
```

## Internal Architecture

### Data Flow
```
Signal Changes → _get_data_dict() → Packet Creation → 
_finish_packet() → _recv() → Callbacks → Statistics Update
```

### Packet Processing Pipeline
1. **Signal sampling** using unified DataCollectionStrategy
2. **Data unpacking** with automatic field handling  
3. **Packet creation** with timing information
4. **Field population** using packet unpack methods
5. **Statistics update** and callback triggering
6. **Queue management** using standard cocotb patterns

### Memory Integration
- Automatic memory writes for received transactions
- Memory read support for validation
- Error handling and logging
- Statistics collection for memory operations

## Usage Patterns

### Creating a Custom Monitor

```python
from CocoTBFramework.components.gaxi.gaxi_monitor_base import GAXIMonitorBase
from CocoTBFramework.components.gaxi.gaxi_packet import GAXIPacket

class CustomGAXIMonitor(GAXIMonitorBase):
    def __init__(self, dut, title, prefix, clock, field_config, 
                 monitor_master_side=True, **kwargs):
        # Determine protocol type based on what we're monitoring
        protocol_type = 'gaxi_master' if monitor_master_side else 'gaxi_slave'
        
        super().__init__(
            dut=dut,
            title=title,
            prefix=prefix,
            clock=clock,
            field_config=field_config,
            protocol_type=protocol_type,
            **kwargs
        )
        
        self.monitor_master_side = monitor_master_side
    
    async def _monitor_recv(self):
        """Custom monitoring implementation"""
        while True:
            await FallingEdge(self.clock)
            
            # Check for handshake
            if (hasattr(self, 'valid_sig') and hasattr(self, 'ready_sig') and
                self.valid_sig.value == 1 and self.ready_sig.value == 1):
                
                # Create packet
                packet = GAXIPacket(self.field_config)
                packet.start_time = get_sim_time('ns')
                
                # Use unified data collection
                data_dict = self._get_data_dict()
                
                # Use unified packet finishing
                self._finish_packet(get_sim_time('ns'), packet, data_dict)
```

### Memory-Integrated Monitor

```python
class MemoryValidatingMonitor(GAXIMonitorBase):
    def __init__(self, dut, title, prefix, clock, field_config, 
                 memory_model, **kwargs):
        super().__init__(
            dut=dut,
            title=title,
            prefix=prefix,
            clock=clock,
            field_config=field_config,
            protocol_type='gaxi_slave',  # Monitor slave side
            memory_model=memory_model,
            **kwargs
        )
        
        self.validation_errors = 0
    
    async def _monitor_recv(self):
        while True:
            await FallingEdge(self.clock)
            
            if self._detect_handshake():
                packet = GAXIPacket(self.field_config)
                packet.start_time = get_sim_time('ns')
                
                # Use unified data collection
                data_dict = self._get_data_dict()
                self._finish_packet(get_sim_time('ns'), packet, data_dict)
                
                # Validate against memory
                await self._validate_transaction(packet)
    
    async def _validate_transaction(self, packet):
        """Validate transaction against expected memory contents"""
        if hasattr(packet, 'cmd') and packet.cmd == 1:  # Read
            # Validate read data against memory
            success, expected_data = self.handle_memory_read(packet)
            if success and hasattr(packet, 'data'):
                if packet.data != expected_data:
                    self.validation_errors += 1
                    self.log.error(f"Data mismatch: expected 0x{expected_data:X}, "
                                  f"got 0x{packet.data:X}")
        
        elif hasattr(packet, 'cmd') and packet.cmd == 2:  # Write
            # Store write data in memory
            self.handle_memory_write(packet)
    
    def _detect_handshake(self):
        """Detect valid/ready handshake"""
        return (hasattr(self, 'valid_sig') and hasattr(self, 'ready_sig') and
                self.valid_sig.value == 1 and self.ready_sig.value == 1)
    
    def get_validation_stats(self):
        """Get validation-specific statistics"""
        base_stats = self.get_base_stats()
        base_stats['validation_errors'] = self.validation_errors
        return base_stats
```

### Protocol Violation Monitor

```python
class ProtocolViolationMonitor(GAXIMonitorBase):
    def __init__(self, dut, title, prefix, clock, field_config, **kwargs):
        super().__init__(
            dut=dut,
            title=title,
            prefix=prefix,
            clock=clock,
            field_config=field_config,
            protocol_type='gaxi_master',
            **kwargs
        )
        
        self.protocol_violations = []
        self.x_z_violations = 0
    
    async def _monitor_recv(self):
        while True:
            await RisingEdge(self.clock)
            
            # Check for protocol violations
            violations = self._check_protocol_violations()
            if violations:
                self.protocol_violations.extend(violations)
                for violation in violations:
                    self.log.warning(f"Protocol violation: {violation}")
            
            # Check for X/Z values
            if self._check_x_z_values():
                self.x_z_violations += 1
                self.log.error("X/Z values detected in signals")
            
            # Normal transaction monitoring
            if self._detect_valid_transaction():
                packet = GAXIPacket(self.field_config)
                packet.start_time = get_sim_time('ns')
                
                data_dict = self._get_data_dict()
                self._finish_packet(get_sim_time('ns'), packet, data_dict)
    
    def _check_protocol_violations(self):
        """Check for protocol-specific violations"""
        violations = []
        
        # Check valid/ready protocol
        if (hasattr(self, 'valid_sig') and hasattr(self, 'ready_sig')):
            valid_val = self.valid_sig.value
            ready_val = self.ready_sig.value
            
            # Add custom protocol checks here
            # Example: Check for invalid signal combinations
            
        return violations
    
    def _check_x_z_values(self):
        """Check for X/Z values in critical signals"""
        try:
            critical_signals = [self.valid_sig, self.ready_sig]
            if hasattr(self, 'data_sig'):
                critical_signals.append(self.data_sig)
            
            for signal in critical_signals:
                if signal and not signal.value.is_resolvable:
                    return True
            return False
        except:
            return True
    
    def _detect_valid_transaction(self):
        """Detect valid transaction for normal monitoring"""
        return (hasattr(self, 'valid_sig') and hasattr(self, 'ready_sig') and
                self.valid_sig.value == 1 and self.ready_sig.value == 1)
    
    def get_violation_stats(self):
        """Get protocol violation statistics"""
        base_stats = self.get_base_stats()
        base_stats.update({
            'protocol_violations': len(self.protocol_violations),
            'x_z_violations': self.x_z_violations,
            'violation_details': self.protocol_violations.copy()
        })
        return base_stats
```

### Statistics Collection Monitor

```python
class StatisticsMonitor(GAXIMonitorBase):
    def __init__(self, dut, title, prefix, clock, field_config, **kwargs):
        super().__init__(
            dut=dut,
            title=title,
            prefix=prefix,
            clock=clock,
            field_config=field_config,
            protocol_type='gaxi_master',
            **kwargs
        )
        
        self.transaction_latencies = []
        self.throughput_samples = []
        self.last_transaction_time = 0
    
    async def _monitor_recv(self):
        while True:
            await FallingEdge(self.clock)
            current_time = get_sim_time('ns')
            
            if self._detect_handshake():
                # Calculate inter-transaction time
                if self.last_transaction_time > 0:
                    inter_time = current_time - self.last_transaction_time
                    self.throughput_samples.append(1e9 / inter_time)  # TPS
                
                self.last_transaction_time = current_time
                
                # Create and process packet
                packet = GAXIPacket(self.field_config)
                packet.start_time = current_time
                
                data_dict = self._get_data_dict()
                self._finish_packet(current_time, packet, data_dict)
                
                # Calculate latency if start time available
                if hasattr(packet, 'start_time') and hasattr(packet, 'end_time'):
                    latency = packet.end_time - packet.start_time
                    self.transaction_latencies.append(latency)
    
    def _detect_handshake(self):
        return (hasattr(self, 'valid_sig') and hasattr(self, 'ready_sig') and
                self.valid_sig.value == 1 and self.ready_sig.value == 1)
    
    def get_performance_stats(self):
        """Get performance statistics"""
        base_stats = self.get_base_stats()
        
        if self.transaction_latencies:
            base_stats['average_latency_ns'] = sum(self.transaction_latencies) / len(self.transaction_latencies)
            base_stats['min_latency_ns'] = min(self.transaction_latencies)
            base_stats['max_latency_ns'] = max(self.transaction_latencies)
        
        if self.throughput_samples:
            base_stats['average_throughput_tps'] = sum(self.throughput_samples) / len(self.throughput_samples)
            base_stats['peak_throughput_tps'] = max(self.throughput_samples)
        
        return base_stats
```

## Integration with CocoTB

### Callback System
```python
# GAXIMonitorBase uses standard cocotb callback system
monitor.add_callback(transaction_handler)

def transaction_handler(packet):
    """Called automatically when packet is received"""
    print(f"Transaction: {packet.formatted()}")
```

### Queue Management
```python
# Standard cocotb queue access
packets = monitor._recvQ  # Direct access (not recommended)
packets = monitor.get_observed_packets()  # Preferred method
```

### Signal Handling
```python
# Automatic signal resolution from GAXIComponentBase
# Supports both automatic discovery and manual mapping
monitor = CustomMonitor(dut, "Monitor", "", clock, field_config,
                       signal_map={'valid': 'custom_valid'})
```

## Error Handling

### Missing Signals
```python
# GAXIMonitorBase handles missing signals gracefully
try:
    data_dict = self._get_data_dict()
except AttributeError as e:
    self.log.warning(f"Signal access error: {e}")
    # Continue with partial data
```

### Memory Operations
```python
# Memory operations return success status
success = self.handle_memory_write(packet)
if not success:
    self.log.warning("Memory write failed - continuing monitoring")
```

### Data Collection Errors
```python
# Data collection handles X/Z values and signal errors
data_dict = self._get_data_dict()
# X/Z values returned as -1, handled automatically
```

## Best Practices

### 1. **Use Unified Methods**
```python
# Prefer unified methods over custom implementations
data_dict = self._get_data_dict()           # Not custom collection
self._finish_packet(time, packet, data)     # Not custom finishing
```

### 2. **Handle Signal Errors Gracefully**
```python
def safe_signal_access(self):
    try:
        return self._get_data_dict()
    except AttributeError:
        return {}  # Return empty dict on signal errors
```

### 3. **Use Memory Integration When Available**
```python
if self.memory_model:
    success = self.handle_memory_write(packet)
    if not success:
        self.log.warning("Memory operation failed")
```

### 4. **Monitor Statistics Regularly**
```python
# Check statistics periodically
if packet_count % 100 == 0:
    stats = self.get_base_stats()
    print(f"Monitored {stats['observed_packets']} packets")
```

### 5. **Implement Protocol-Specific Checks**
```python
class ProtocolSpecificMonitor(GAXIMonitorBase):
    def _validate_transaction(self, packet):
        """Add protocol-specific validation"""
        if hasattr(packet, 'addr') and packet.addr % 4 != 0:
            self.log.error("Unaligned address detected")
```

GAXIMonitorBase provides a solid foundation for GAXI monitoring components, eliminating code duplication while maintaining flexibility for protocol-specific monitoring requirements.