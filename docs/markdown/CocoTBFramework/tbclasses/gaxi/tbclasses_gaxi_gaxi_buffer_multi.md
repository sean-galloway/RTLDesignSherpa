# gaxi_buffer_multi.py

Multi-signal GAXI buffer testbench with enhanced timing and completion checking. This testbench provides comprehensive testing for GAXI components with multiple independent signal paths, featuring fixed timing issues and improved verification capabilities.

## Overview

The `GaxiMultiBufferTB` class extends GAXI testing to support multi-signal configurations with independent data streams. It includes significant timing improvements and completion checking to ensure robust verification of complex buffer implementations.

### Key Features
- **Enhanced timing with completion checking** - Fixed timing issues from previous versions
- **Multiple independent signal paths** support
- **Buffer-depth-aware delay calculations** for accurate timing
- **Timeout protection** preventing infinite waits
- **Concurrent stream testing** capabilities
- **Enhanced verification methods** for better error detection
- **FlexConfigGen integration** for comprehensive randomization
- **Memory model integration** for dual-stream verification

### Supported DUT Types
- `gaxi_fifo_sync_multi`: Multi-signal synchronous FIFO buffer
- `gaxi_skid_buffer_multi`: Multi-signal skid buffer with flow control

## Class Definition

```python
class GaxiMultiBufferTB(TBBase):
    """
    Updated testbench for multi-signal GAXI components with FIXED timing and completion checking.
    
    Supports gaxi_fifo_sync_multi and gaxi_skid_buffer_multi components.
    All existing APIs are preserved for test runner compatibility.
    """
    
    def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None):
```

## Timing Enhancements

### Fixed Timing Issues

The testbench addresses several critical timing issues found in earlier versions:

**Completion Checking**:
```python
# Wait for expected number of packets to be received before verification
async def wait_for_completion(self, expected_packets, timeout_cycles=None):
    """
    Wait for expected packet count with enhanced timeout protection
    
    Parameters:
    - expected_packets: Number of packets expected
    - timeout_cycles: Maximum cycles to wait (calculated if None)
    """
    
    if timeout_cycles is None:
        # Calculate timeout based on buffer characteristics
        base_delay = self.BASE_COMPLETION_DELAY
        buffer_delay = self.TEST_DEPTH * 2  # Account for buffer depth
        mode_delay = 10 if self.TEST_MODE == 'fifo' else 5
        timeout_cycles = base_delay + buffer_delay + mode_delay
    
    received_count = 0
    for cycle in range(timeout_cycles):
        # Check if expected packets received
        if self.get_received_packet_count() >= expected_packets:
            self.log.debug(f"Completion achieved at cycle {cycle}")
            return True
            
        await RisingEdge(self.wr_clk)
        
        # Update received count periodically
        if cycle % 10 == 0:
            received_count = self.get_received_packet_count()
            self.log.debug(f"Cycle {cycle}: {received_count}/{expected_packets} packets received")
    
    self.log.error(f"Timeout after {timeout_cycles} cycles: {received_count}/{expected_packets} received")
    return False
```

**Buffer-Depth-Aware Delays**:
```python
# Enhanced timing calculations based on buffer characteristics
def calculate_expected_delay(self, num_packets):
    """Calculate expected delay based on buffer and mode characteristics"""
    
    # Base delay for signal propagation
    base_delay = 2
    
    # Buffer-specific delays
    if self.TEST_MODE == 'skid':
        # Skid buffers have minimal additional delay
        buffer_delay = max(1, self.TEST_DEPTH // 8)
    elif self.TEST_MODE == 'fifo':
        # FIFO buffers may have more complex timing
        buffer_delay = max(2, self.TEST_DEPTH // 4)
    else:
        buffer_delay = 1
    
    # Packet-count-based delay
    packet_delay = num_packets // 4
    
    total_delay = base_delay + buffer_delay + packet_delay
    self.log.debug(f"Expected delay: {total_delay} cycles for {num_packets} packets")
    
    return total_delay
```

### Timeout Protection

Enhanced timeout protection prevents infinite waits:

```python
# Timeout configuration with mode-specific values
self.COMPLETION_TIMEOUT_CYCLES = max(1000, self.TEST_DEPTH * 10)
self.BASE_COMPLETION_DELAY = 50

# Adaptive timeout based on test conditions
def get_adaptive_timeout(self, operation_type, packet_count):
    """Get adaptive timeout based on operation and system state"""
    
    base_timeout = self.COMPLETION_TIMEOUT_CYCLES
    
    # Adjust for operation type
    if operation_type == 'burst':
        timeout_multiplier = 1.5
    elif operation_type == 'random':
        timeout_multiplier = 2.0
    else:
        timeout_multiplier = 1.0
    
    # Adjust for packet count
    packet_multiplier = max(1.0, packet_count / 50.0)
    
    adaptive_timeout = int(base_timeout * timeout_multiplier * packet_multiplier)
    self.log.debug(f"Adaptive timeout: {adaptive_timeout} cycles for {operation_type}")
    
    return adaptive_timeout
```

## Multi-Signal Architecture

### Field Configuration for Multi-Signal

The testbench supports multi-field configurations with proper width handling:

```python
# Multi-signal field configuration
def setup_multi_signal_fields(self):
    """Setup field configuration for multi-signal testing"""
    
    # Use base configuration from FIELD_CONFIGS
    base_config = FIELD_CONFIGS.get('field', {
        'addr': {'bits': self.AW, 'start_bit': 0},
        'ctrl': {'bits': self.CW, 'start_bit': self.AW},
        'data0': {'bits': self.DW, 'start_bit': self.AW + self.CW},
        'data1': {'bits': self.DW, 'start_bit': self.AW + self.CW + self.DW}
    })
    
    # Create normalized field configuration
    self.field_config = FieldConfig.validate_and_create(base_config)
    
    # Update field widths from test parameters
    self.field_config.update_field_width('addr', self.AW)
    self.field_config.update_field_width('ctrl', self.CW)
    self.field_config.update_field_width('data0', self.DW)
    self.field_config.update_field_width('data1', self.DW)
    
    self.log.debug(f"Multi-signal field configuration:\n{self.field_config}")
```

### Component Configuration

Multi-signal components with enhanced monitoring:

```python
# Create multi-signal masters and slaves
self.write_master_a = GAXIMaster(
    dut, 'write_master_a', 'a_', self.wr_clk,
    field_config=self.field_config,
    log=self.log
)

self.write_master_b = GAXIMaster(
    dut, 'write_master_b', 'b_', self.wr_clk,
    field_config=self.field_config,
    log=self.log
)

self.read_slave_a = GAXISlave(
    dut, 'read_slave_a', 'a_', self.rd_clk,
    field_config=self.field_config,
    log=self.log
)

self.read_slave_b = GAXISlave(
    dut, 'read_slave_b', 'b_', self.rd_clk,
    field_config=self.field_config,
    log=self.log
)

# Enhanced monitors for multi-signal observation
self.write_monitor_a = GAXIMonitor(
    dut, 'write_monitor_a', 'a_', self.wr_clk,
    field_config=self.field_config,
    is_slave=False,
    mode=self.TEST_MODE,
    log=self.log
)

self.write_monitor_b = GAXIMonitor(
    dut, 'write_monitor_b', 'b_', self.wr_clk,
    field_config=self.field_config,
    is_slave=False,
    mode=self.TEST_MODE,
    log=self.log
)
```

## Core Testing Methods

### Concurrent Stream Testing

```python
async def test_concurrent_streams(self, num_packets=50):
    """
    Test multiple concurrent data streams with enhanced timing
    
    Parameters:
    - num_packets: Number of packets per stream
    """
    
    self.log.info(f"Starting concurrent stream test with {num_packets} packets per stream")
    
    # Generate packet sequences for both streams
    packets_a = self.generate_packet_sequence(num_packets, stream_id='A')
    packets_b = self.generate_packet_sequence(num_packets, stream_id='B')
    
    # Start concurrent transmission
    async def send_stream_a():
        for packet in packets_a:
            await self.write_master_a.drive_packet(packet)
            await Timer(random.randint(1, 5), units='ns')  # Variable delay
    
    async def send_stream_b():
        for packet in packets_b:
            await self.write_master_b.drive_packet(packet)
            await Timer(random.randint(1, 5), units='ns')  # Variable delay
    
    # Start both streams concurrently
    await cocotb.start(send_stream_a())
    await cocotb.start(send_stream_b())
    
    # Wait for completion with enhanced timeout
    expected_total = num_packets * 2
    timeout = self.get_adaptive_timeout('concurrent', expected_total)
    
    completion_success = await self.wait_for_completion(expected_total, timeout)
    if not completion_success:
        self.log.error("Concurrent stream test failed due to timeout")
        self.total_errors += 1
        return
    
    # Verify received packets
    received_a = await self.collect_stream_packets('A', num_packets)
    received_b = await self.collect_stream_packets('B', num_packets)
    
    # Comprehensive verification
    errors_a = self.verify_packet_sequence(packets_a, received_a, 'Stream A')
    errors_b = self.verify_packet_sequence(packets_b, received_b, 'Stream B')
    
    total_stream_errors = errors_a + errors_b
    self.total_errors += total_stream_errors
    
    self.log.info(f"Concurrent stream test completed: {total_stream_errors} errors")
```

### Enhanced Burst Testing

```python
async def test_enhanced_burst(self, burst_size=16, num_bursts=5):
    """
    Enhanced burst testing with completion checking
    
    Parameters:
    - burst_size: Size of each burst
    - num_bursts: Number of burst sequences
    """
    
    self.log.info(f"Enhanced burst test: {num_bursts} bursts of {burst_size} packets")
    
    for burst_num in range(num_bursts):
        self.log.debug(f"Starting burst {burst_num + 1}/{num_bursts}")
        
        # Generate burst packets
        burst_packets = self.generate_burst_sequence(burst_size, burst_num)
        
        # Send burst with minimal delay
        for packet in burst_packets:
            await self.write_master_a.drive_packet(packet)
            # Minimal inter-packet delay for burst
            await Timer(1, units='ns')
        
        # Wait for burst completion
        expected_delay = self.calculate_expected_delay(burst_size)
        await Timer(expected_delay, units='clk')
        
        # Verify burst completion
        burst_timeout = self.get_adaptive_timeout('burst', burst_size)
        completion = await self.wait_for_completion(burst_size, burst_timeout)
        
        if not completion:
            self.log.error(f"Burst {burst_num} failed to complete")
            self.total_errors += 1
            continue
        
        # Collect and verify burst packets
        received_burst = await self.collect_burst_packets(burst_size)
        burst_errors = self.verify_packet_sequence(burst_packets, received_burst, f'Burst {burst_num}')
        self.total_errors += burst_errors
        
        # Inter-burst delay
        await Timer(10, units='clk')
    
    self.log.info(f"Enhanced burst test completed with {self.total_errors} total errors")
```

### Stress Testing with Timing Validation

```python
async def test_stress_with_timing(self, num_packets=100):
    """
    Stress test with comprehensive timing validation
    
    Parameters:
    - num_packets: Number of packets for stress testing
    """
    
    self.log.info(f"Stress test with timing validation: {num_packets} packets")
    
    # Record start time
    start_time = get_sim_time('ns')
    packets_sent = []
    
    # Stress transmission with variable delays
    for i in range(num_packets):
        packet = self.generate_stress_packet(i)
        packet.start_time = get_sim_time('ns')
        
        await self.write_master_a.drive_packet(packet)
        packets_sent.append(packet)
        
        # Variable delay pattern for stress
        if i % 10 == 0:
            await Timer(20, units='ns')  # Occasional longer delay
        elif i % 3 == 0:
            await Timer(5, units='ns')   # Medium delay
        else:
            await Timer(1, units='ns')   # Minimal delay
    
    # Wait for completion with stress-appropriate timeout
    stress_timeout = self.get_adaptive_timeout('stress', num_packets)
    completion = await self.wait_for_completion(num_packets, stress_timeout)
    
    if not completion:
        self.log.error("Stress test failed due to completion timeout")
        self.total_errors += 1
        return
    
    # Collect all received packets
    received_packets = await self.collect_all_packets(num_packets)
    
    # Comprehensive timing and data verification
    timing_errors = self.verify_timing_constraints(packets_sent, received_packets)
    data_errors = self.verify_packet_sequence(packets_sent, received_packets, 'Stress Test')
    
    end_time = get_sim_time('ns')
    total_time = end_time - start_time
    throughput = (num_packets * 1e9) / total_time  # Packets per second
    
    self.total_errors += timing_errors + data_errors
    
    self.log.info(f"Stress test completed:")
    self.log.info(f"  Total time: {total_time:.1f} ns")
    self.log.info(f"  Throughput: {throughput:.1f} packets/sec")
    self.log.info(f"  Timing errors: {timing_errors}")
    self.log.info(f"  Data errors: {data_errors}")
```

## Enhanced Verification Methods

### Timing Constraint Verification

```python
def verify_timing_constraints(self, sent_packets, received_packets):
    """
    Verify timing constraints for multi-signal operations
    
    Parameters:
    - sent_packets: List of sent packets with timestamps
    - received_packets: List of received packets with timestamps
    
    Returns: Number of timing constraint violations
    """
    
    timing_errors = 0
    
    if len(sent_packets) != len(received_packets):
        self.log.error(f"Packet count mismatch: sent={len(sent_packets)}, received={len(received_packets)}")
        return len(sent_packets)  # Consider all as errors
    
    for i, (sent, received) in enumerate(zip(sent_packets, received_packets)):
        if not hasattr(sent, 'start_time') or not hasattr(received, 'end_time'):
            continue
        
        latency = received.end_time - sent.start_time
        expected_max_latency = self.calculate_max_expected_latency()
        
        if latency > expected_max_latency:
            timing_errors += 1
            self.log.error(f"Packet {i} timing violation: latency={latency:.1f}ns, max_expected={expected_max_latency:.1f}ns")
        else:
            self.log.debug(f"Packet {i} timing OK: latency={latency:.1f}ns")
    
    return timing_errors

def calculate_max_expected_latency(self):
    """Calculate maximum expected latency based on buffer characteristics"""
    
    # Base latency for signal propagation
    base_latency = 20.0  # ns
    
    # Buffer-dependent latency
    if self.TEST_MODE == 'skid':
        buffer_latency = self.TEST_DEPTH * 2.0  # Skid buffer latency
    elif self.TEST_MODE == 'fifo':
        buffer_latency = self.TEST_DEPTH * 5.0  # FIFO buffer latency
    else:
        buffer_latency = self.TEST_DEPTH * 1.0
    
    # Clock period dependent latency
    clock_latency = float(self.TEST_CLK_WR) * 3.0
    
    max_latency = base_latency + buffer_latency + clock_latency
    self.log.debug(f"Maximum expected latency: {max_latency:.1f}ns")
    
    return max_latency
```

### Packet Sequence Verification

```python
def verify_packet_sequence(self, sent_sequence, received_sequence, test_name):
    """
    Comprehensive packet sequence verification
    
    Parameters:
    - sent_sequence: Original packet sequence
    - received_sequence: Received packet sequence
    - test_name: Name of test for error reporting
    
    Returns: Number of verification errors
    """
    
    sequence_errors = 0
    
    # Check sequence length
    if len(sent_sequence) != len(received_sequence):
        sequence_errors += abs(len(sent_sequence) - len(received_sequence))
        self.log.error(f"{test_name}: Sequence length mismatch - sent={len(sent_sequence)}, received={len(received_sequence)}")
    
    # Verify each packet in sequence
    min_length = min(len(sent_sequence), len(received_sequence))
    for i in range(min_length):
        sent_packet = sent_sequence[i]
        received_packet = received_sequence[i]
        
        # Field-by-field verification
        field_errors = self.verify_multi_field_packet(sent_packet, received_packet, i)
        sequence_errors += field_errors
        
        if field_errors > 0:
            self.log.error(f"{test_name}: Packet {i} failed verification with {field_errors} field errors")
        else:
            self.log.debug(f"{test_name}: Packet {i} verified successfully")
    
    # Log sequence verification summary
    if sequence_errors == 0:
        self.log.info(f"{test_name}: Sequence verification PASSED - {min_length} packets verified")
    else:
        self.log.error(f"{test_name}: Sequence verification FAILED - {sequence_errors} errors in {min_length} packets")
    
    return sequence_errors

def verify_multi_field_packet(self, sent_packet, received_packet, packet_index):
    """Verify individual multi-field packet"""
    
    field_errors = 0
    fields_to_check = ['addr', 'ctrl', 'data0', 'data1']
    
    for field in fields_to_check:
        sent_val = getattr(sent_packet, field, None)
        recv_val = getattr(received_packet, field, None)
        
        if sent_val != recv_val:
            field_errors += 1
            self.log.error(f"Packet {packet_index} field '{field}': sent=0x{sent_val:X}, received=0x{recv_val:X}")
    
    return field_errors
```

## Usage Examples

### Basic Multi-Signal Testing

```python
import cocotb
import os
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_multi import GaxiMultiBufferTB

@cocotb.test()
async def test_multi_signal_basic(dut):
    # Configure multi-signal environment
    os.environ['TEST_DEPTH'] = '16'
    os.environ['TEST_ADDR_WIDTH'] = '32'
    os.environ['TEST_CTRL_WIDTH'] = '8'
    os.environ['TEST_DATA_WIDTH'] = '32'
    os.environ['TEST_MODE'] = 'skid'
    os.environ['TEST_KIND'] = 'sync'
    
    # Create multi-signal testbench
    tb = GaxiMultiBufferTB(dut, wr_clk=dut.clk, wr_rstn=dut.rstn)
    await tb.initialize()
    
    # Run concurrent stream testing
    await tb.test_concurrent_streams(num_packets=50)
    
    # Verify results
    assert tb.total_errors == 0, f"Multi-signal test failed with {tb.total_errors} errors"
```

### Advanced Multi-Signal Testing

```python
@cocotb.test()
async def test_multi_signal_comprehensive(dut):
    # Advanced configuration with larger buffers
    os.environ['TEST_DEPTH'] = '64'
    os.environ['TEST_ADDR_WIDTH'] = '32'
    os.environ['TEST_CTRL_WIDTH'] = '16'
    os.environ['TEST_DATA_WIDTH'] = '64'
    os.environ['TEST_MODE'] = 'fifo'
    os.environ['TEST_KIND'] = 'async'
    os.environ['TEST_CLK_WR'] = '8'
    os.environ['TEST_CLK_RD'] = '10'
    
    tb = GaxiMultiBufferTB(
        dut,
        wr_clk=dut.wr_clk,
        wr_rstn=dut.wr_rstn,
        rd_clk=dut.rd_clk,
        rd_rstn=dut.rd_rstn
    )
    await tb.initialize()
    
    # Comprehensive test suite
    await tb.test_enhanced_burst(burst_size=32, num_bursts=8)
    await tb.test_concurrent_streams(num_packets=100)
    await tb.test_stress_with_timing(num_packets=200)
    
    # Generate detailed report
    report = tb.generate_enhanced_report()
    tb.log.info(f"Comprehensive test report:\n{report}")
```

The `gaxi_buffer_multi.py` component provides robust multi-signal testing capabilities with enhanced timing accuracy, comprehensive verification, and advanced completion checking for thorough validation of complex GAXI buffer implementations.