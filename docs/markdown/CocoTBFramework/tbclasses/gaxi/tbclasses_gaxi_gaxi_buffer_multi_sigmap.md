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

# gaxi_buffer_multi_sigmap.py

Multi-signal GAXI buffer testbench with signal mapping capabilities. This testbench extends the multi-signal testing framework to support custom signal naming conventions and flexible signal mapping, making it suitable for integration with legacy systems and non-standard designs.

## Overview

The `GaxiMultiSigMapBufferTB` class provides all the capabilities of the multi-signal testbench while adding flexible signal mapping functionality. This enables testing of DUTs with non-standard signal naming conventions or complex signal hierarchies.

### Key Features
- **Flexible signal mapping** for non-standard naming conventions
- **Custom prefix/suffix handling** for complex signal hierarchies
- **Legacy system integration** support
- **Enhanced timing with completion checking** inherited from multi-signal base
- **Multiple signal path support** with configurable naming
- **Backward compatibility** with existing test frameworks
- **Dynamic signal resolution** and validation

### Supported DUT Types
- `gaxi_fifo_sync_multi`: Multi-signal synchronous FIFO with custom signals
- `gaxi_skid_buffer_multi`: Multi-signal skid buffer with custom signals
- Legacy GAXI implementations with non-standard naming
- Custom GAXI variants with unique signal hierarchies

## Class Definition

```python
class GaxiMultiSigMapBufferTB(TBBase):
    """
    Multi-signal GAXI buffer testbench with FIXED timing and completion checking.
    
    Extends multi-signal capabilities with flexible signal mapping for 
    non-standard naming conventions and legacy system integration.
    """
    
    def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None, signal_map=None):
```

## Signal Mapping System

### Signal Map Configuration

The signal mapping system allows complete customization of signal names:

```python
# Default signal mapping (can be overridden)
DEFAULT_SIGNAL_MAP = {
    'write_channel_a': {
        'valid': 'i_a_valid',
        'ready': 'o_a_ready', 
        'addr': 'i_a_addr',
        'ctrl': 'i_a_ctrl',
        'data0': 'i_a_data0',
        'data1': 'i_a_data1'
    },
    'write_channel_b': {
        'valid': 'i_b_valid',
        'ready': 'o_b_ready',
        'addr': 'i_b_addr', 
        'ctrl': 'i_b_ctrl',
        'data0': 'i_b_data0',
        'data1': 'i_b_data1'
    },
    'read_channel_a': {
        'valid': 'o_a_valid',
        'ready': 'i_a_ready',
        'addr': 'o_a_addr',
        'ctrl': 'o_a_ctrl', 
        'data0': 'o_a_data0',
        'data1': 'o_a_data1'
    },
    'read_channel_b': {
        'valid': 'o_b_valid',
        'ready': 'i_b_ready',
        'addr': 'o_b_addr',
        'ctrl': 'o_b_ctrl',
        'data0': 'o_b_data0',
        'data1': 'o_b_data1'
    }
}
```

### Custom Signal Mapping

Users can provide custom signal mappings for various scenarios:

```python
# Example: Legacy system with different naming
LEGACY_SIGNAL_MAP = {
    'write_channel_a': {
        'valid': 'inp_ch0_vld',
        'ready': 'out_ch0_rdy',
        'addr': 'inp_ch0_address',
        'ctrl': 'inp_ch0_control',
        'data0': 'inp_ch0_payload_0',
        'data1': 'inp_ch0_payload_1'
    },
    'write_channel_b': {
        'valid': 'inp_ch1_vld',
        'ready': 'out_ch1_rdy',
        'addr': 'inp_ch1_address',
        'ctrl': 'inp_ch1_control',
        'data0': 'inp_ch1_payload_0',
        'data1': 'inp_ch1_payload_1'
    },
    'read_channel_a': {
        'valid': 'out_ch0_vld',
        'ready': 'inp_ch0_rdy',
        'addr': 'out_ch0_address',
        'ctrl': 'out_ch0_control',
        'data0': 'out_ch0_payload_0',
        'data1': 'out_ch0_payload_1'
    },
    'read_channel_b': {
        'valid': 'out_ch1_vld',
        'ready': 'inp_ch1_rdy',
        'addr': 'out_ch1_address',
        'ctrl': 'out_ch1_control',
        'data0': 'out_ch1_payload_0',
        'data1': 'out_ch1_payload_1'
    }
}

# Example: Hierarchical signal naming
HIERARCHICAL_SIGNAL_MAP = {
    'write_channel_a': {
        'valid': 'bus_interface.input_ports.channel_a.valid',
        'ready': 'bus_interface.input_ports.channel_a.ready',
        'addr': 'bus_interface.input_ports.channel_a.address',
        'ctrl': 'bus_interface.input_ports.channel_a.control',
        'data0': 'bus_interface.input_ports.channel_a.data_low',
        'data1': 'bus_interface.input_ports.channel_a.data_high'
    },
    # ... additional channels
}
```

### Dynamic Signal Resolution

The testbench includes intelligent signal resolution with fallback mechanisms:

```python
def resolve_signal_mapping(self, signal_map=None):
    """
    Resolve signal mapping with intelligent fallbacks
    
    Parameters:
    - signal_map: Custom signal mapping dictionary
    
    Returns: Resolved signal mapping with validation
    """
    
    # Start with default mapping
    resolved_map = copy.deepcopy(self.DEFAULT_SIGNAL_MAP)
    
    # Apply custom mapping if provided
    if signal_map:
        for channel, signals in signal_map.items():
            if channel in resolved_map:
                resolved_map[channel].update(signals)
            else:
                resolved_map[channel] = signals
    
    # Validate signal existence
    validated_map = {}
    for channel, signals in resolved_map.items():
        validated_signals = {}
        for signal_type, signal_name in signals.items():
            # Try direct signal access
            signal_obj = self._find_signal(signal_name)
            if signal_obj is not None:
                validated_signals[signal_type] = signal_name
                self.log.debug(f"Found signal: {channel}.{signal_type} -> {signal_name}")
            else:
                # Try alternative naming conventions
                alternative_names = self._generate_alternative_names(signal_name, signal_type)
                found = False
                for alt_name in alternative_names:
                    alt_signal = self._find_signal(alt_name)
                    if alt_signal is not None:
                        validated_signals[signal_type] = alt_name
                        self.log.debug(f"Found alternative signal: {channel}.{signal_type} -> {alt_name}")
                        found = True
                        break
                
                if not found:
                    self.log.warning(f"Signal not found: {channel}.{signal_type} -> {signal_name}")
        
        if validated_signals:
            validated_map[channel] = validated_signals
    
    return validated_map

def _find_signal(self, signal_path):
    """Find signal in DUT hierarchy using dot notation"""
    try:
        # Handle hierarchical paths
        if '.' in signal_path:
            parts = signal_path.split('.')
            current = self.dut
            for part in parts:
                current = getattr(current, part)
            return current
        else:
            # Direct signal access
            return getattr(self.dut, signal_path, None)
    except AttributeError:
        return None

def _generate_alternative_names(self, base_name, signal_type):
    """Generate alternative signal names for common naming conventions"""
    alternatives = [base_name]
    
    # Common variations
    base_variations = [
        base_name.lower(),
        base_name.upper(),
        base_name.replace('_', ''),
        base_name.replace('_', '.'),
    ]
    
    # Signal-type-specific variations
    if signal_type == 'valid':
        base_variations.extend([
            base_name.replace('valid', 'vld'),
            base_name.replace('valid', 'v'),
            base_name.replace('vld', 'valid')
        ])
    elif signal_type == 'ready':
        base_variations.extend([
            base_name.replace('ready', 'rdy'),
            base_name.replace('ready', 'r'),
            base_name.replace('rdy', 'ready')
        ])
    
    alternatives.extend(base_variations)
    return list(set(alternatives))  # Remove duplicates
```

## Enhanced Component Creation

### Signal-Map-Aware Component Factory

The testbench creates components using the resolved signal mapping:

```python
def create_mapped_components(self):
    """Create components using resolved signal mapping"""
    
    # Create write masters with custom signal mapping
    self.write_master_a = GAXIMaster(
        self.dut, 'write_master_a', '',
        self.wr_clk,
        field_config=self.field_config,
        signal_map=self.signal_map.get('write_channel_a', {}),
        log=self.log
    )
    
    self.write_master_b = GAXIMaster(
        self.dut, 'write_master_b', '',
        self.wr_clk,
        field_config=self.field_config,
        signal_map=self.signal_map.get('write_channel_b', {}),
        log=self.log
    )
    
    # Create read slaves with custom signal mapping
    self.read_slave_a = GAXISlave(
        self.dut, 'read_slave_a', '',
        self.rd_clk,
        field_config=self.field_config,
        signal_map=self.signal_map.get('read_channel_a', {}),
        log=self.log
    )
    
    self.read_slave_b = GAXISlave(
        self.dut, 'read_slave_b', '',
        self.rd_clk,
        field_config=self.field_config,
        signal_map=self.signal_map.get('read_channel_b', {}),
        log=self.log
    )
    
    # Create monitors with signal mapping
    self.write_monitor_a = GAXIMonitor(
        self.dut, 'write_monitor_a', '',
        self.wr_clk,
        field_config=self.field_config,
        is_slave=False,
        signal_map=self.signal_map.get('write_channel_a', {}),
        log=self.log
    )
    
    self.write_monitor_b = GAXIMonitor(
        self.dut, 'write_monitor_b', '',
        self.wr_clk,
        field_config=self.field_config,
        is_slave=False,
        signal_map=self.signal_map.get('write_channel_b', {}),
        log=self.log
    )
    
    self.log.info("Created components with custom signal mapping")
```

## Advanced Testing Methods

### Signal Mapping Validation

```python
async def test_signal_mapping_validation(self):
    """
    Test signal mapping validation and connectivity
    """
    
    self.log.info("Testing signal mapping validation")
    
    validation_errors = 0
    
    # Test each channel's signal connectivity
    for channel_name, channel_signals in self.signal_map.items():
        self.log.debug(f"Validating channel: {channel_name}")
        
        for signal_type, signal_path in channel_signals.items():
            # Verify signal exists and is accessible
            signal_obj = self._find_signal(signal_path)
            if signal_obj is None:
                validation_errors += 1
                self.log.error(f"Signal mapping error: {channel_name}.{signal_type} -> {signal_path} not found")
                continue
            
            # Test signal read/write capability
            try:
                # Try to read current value
                current_value = signal_obj.value
                self.log.debug(f"Signal {signal_path} current value: {current_value}")
                
                # For input signals, try to drive a test value
                if signal_type in ['valid', 'addr', 'ctrl', 'data0', 'data1']:
                    if 'input' in channel_name or 'write' in channel_name:
                        original_value = signal_obj.value
                        signal_obj.value = 0
                        await RisingEdge(self.wr_clk)
                        signal_obj.value = original_value
                        self.log.debug(f"Successfully tested driving {signal_path}")
                
            except Exception as e:
                validation_errors += 1
                self.log.error(f"Signal access error for {signal_path}: {e}")
    
    if validation_errors == 0:
        self.log.info("Signal mapping validation PASSED")
    else:
        self.log.error(f"Signal mapping validation FAILED: {validation_errors} errors")
        self.total_errors += validation_errors
    
    return validation_errors == 0
```

### Mapped Concurrent Testing

```python
async def test_mapped_concurrent_streams(self, num_packets=50):
    """
    Test concurrent streams using mapped signals
    
    Parameters:
    - num_packets: Number of packets per stream
    """
    
    self.log.info(f"Testing mapped concurrent streams: {num_packets} packets per stream")
    
    # Validate signal mapping before testing
    mapping_valid = await self.test_signal_mapping_validation()
    if not mapping_valid:
        self.log.error("Signal mapping validation failed, skipping concurrent test")
        return
    
    # Generate test packets for both channels
    packets_a = self.generate_mapped_packet_sequence(num_packets, 'channel_a')
    packets_b = self.generate_mapped_packet_sequence(num_packets, 'channel_b')
    
    # Send packets concurrently using mapped signals
    async def send_mapped_stream_a():
        for i, packet in enumerate(packets_a):
            await self.write_master_a.drive_packet(packet)
            self.log.debug(f"Channel A packet {i} sent via mapped signals")
            await Timer(random.randint(2, 8), units='ns')
    
    async def send_mapped_stream_b():
        for i, packet in enumerate(packets_b):
            await self.write_master_b.drive_packet(packet)
            self.log.debug(f"Channel B packet {i} sent via mapped signals")
            await Timer(random.randint(2, 8), units='ns')
    
    # Start concurrent transmission
    await cocotb.start(send_mapped_stream_a())
    await cocotb.start(send_mapped_stream_b())
    
    # Wait for completion with mapped signal monitoring
    expected_total = num_packets * 2
    timeout = self.get_adaptive_timeout('mapped_concurrent', expected_total)
    
    completion_success = await self.wait_for_mapped_completion(expected_total, timeout)
    if not completion_success:
        self.log.error("Mapped concurrent streams test failed due to timeout")
        self.total_errors += 1
        return
    
    # Verify received packets using mapped signals
    received_a = await self.collect_mapped_packets('channel_a', num_packets)
    received_b = await self.collect_mapped_packets('channel_b', num_packets)
    
    # Comprehensive verification
    errors_a = self.verify_mapped_packet_sequence(packets_a, received_a, 'Mapped Channel A')
    errors_b = self.verify_mapped_packet_sequence(packets_b, received_b, 'Mapped Channel B')
    
    total_mapped_errors = errors_a + errors_b
    self.total_errors += total_mapped_errors
    
    self.log.info(f"Mapped concurrent streams test completed: {total_mapped_errors} errors")

async def wait_for_mapped_completion(self, expected_packets, timeout_cycles):
    """Wait for completion using mapped signal monitoring"""
    
    received_count = 0
    for cycle in range(timeout_cycles):
        # Monitor completion using mapped signals
        current_count_a = self.count_mapped_packets('channel_a')
        current_count_b = self.count_mapped_packets('channel_b')
        received_count = current_count_a + current_count_b
        
        if received_count >= expected_packets:
            self.log.debug(f"Mapped completion achieved at cycle {cycle}: {received_count}/{expected_packets}")
            return True
        
        await RisingEdge(self.wr_clk)
        
        # Periodic progress reporting
        if cycle % 50 == 0:
            self.log.debug(f"Mapped completion cycle {cycle}: {received_count}/{expected_packets} packets")
    
    self.log.error(f"Mapped completion timeout after {timeout_cycles} cycles: {received_count}/{expected_packets}")
    return False
```

## Usage Examples

### Basic Signal Mapping

```python
import cocotb
import os
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_multi_sigmap import GaxiMultiSigMapBufferTB

@cocotb.test()
async def test_custom_signal_mapping(dut):
    # Configure environment
    os.environ['TEST_DEPTH'] = '16'
    os.environ['TEST_ADDR_WIDTH'] = '32'
    os.environ['TEST_CTRL_WIDTH'] = '8'
    os.environ['TEST_DATA_WIDTH'] = '32'
    
    # Define custom signal mapping
    custom_map = {
        'write_channel_a': {
            'valid': 'input_ch0_valid',
            'ready': 'output_ch0_ready',
            'addr': 'input_ch0_addr',
            'ctrl': 'input_ch0_ctrl',
            'data0': 'input_ch0_data_low',
            'data1': 'input_ch0_data_high'
        },
        'read_channel_a': {
            'valid': 'output_ch0_valid',
            'ready': 'input_ch0_ready',
            'addr': 'output_ch0_addr',
            'ctrl': 'output_ch0_ctrl',
            'data0': 'output_ch0_data_low',
            'data1': 'output_ch0_data_high'
        }
    }
    
    # Create testbench with custom mapping
    tb = GaxiMultiSigMapBufferTB(
        dut,
        wr_clk=dut.clk,
        wr_rstn=dut.rstn,
        signal_map=custom_map
    )
    await tb.initialize()
    
    # Test with custom signal mapping
    await tb.test_mapped_concurrent_streams(num_packets=30)
    
    assert tb.total_errors == 0, f"Custom mapping test failed with {tb.total_errors} errors"
```

### Legacy System Integration

```python
@cocotb.test()
async def test_legacy_system_integration(dut):
    # Legacy signal naming convention
    legacy_map = {
        'write_channel_a': {
            'valid': 'legacy_inp_vld_0',
            'ready': 'legacy_out_rdy_0',
            'addr': 'legacy_inp_addr_0',
            'ctrl': 'legacy_inp_cmd_0',
            'data0': 'legacy_inp_payload_0_low',
            'data1': 'legacy_inp_payload_0_high'
        },
        'write_channel_b': {
            'valid': 'legacy_inp_vld_1',
            'ready': 'legacy_out_rdy_1',
            'addr': 'legacy_inp_addr_1',
            'ctrl': 'legacy_inp_cmd_1',
            'data0': 'legacy_inp_payload_1_low',
            'data1': 'legacy_inp_payload_1_high'
        },
        'read_channel_a': {
            'valid': 'legacy_out_vld_0',
            'ready': 'legacy_inp_rdy_0',
            'addr': 'legacy_out_addr_0',
            'ctrl': 'legacy_out_cmd_0',
            'data0': 'legacy_out_payload_0_low',
            'data1': 'legacy_out_payload_0_high'
        },
        'read_channel_b': {
            'valid': 'legacy_out_vld_1',
            'ready': 'legacy_inp_rdy_1',
            'addr': 'legacy_out_addr_1',
            'ctrl': 'legacy_out_cmd_1',
            'data0': 'legacy_out_payload_1_low',
            'data1': 'legacy_out_payload_1_high'
        }
    }
    
    tb = GaxiMultiSigMapBufferTB(
        dut,
        wr_clk=dut.legacy_clk,
        wr_rstn=dut.legacy_reset_n,
        signal_map=legacy_map
    )
    await tb.initialize()
    
    # Validate legacy signal mapping
    await tb.test_signal_mapping_validation()
    
    # Run legacy system tests
    await tb.test_mapped_concurrent_streams(num_packets=40)
    
    # Generate legacy system report
    report = tb.generate_legacy_compatibility_report()
    tb.log.info(f"Legacy integration report:\n{report}")
```

### Hierarchical Signal Testing

```python
@cocotb.test()
async def test_hierarchical_signals(dut):
    # Hierarchical signal mapping
    hierarchical_map = {
        'write_channel_a': {
            'valid': 'bus_interface.input_side.ch0.handshake.valid',
            'ready': 'bus_interface.input_side.ch0.handshake.ready',
            'addr': 'bus_interface.input_side.ch0.payload.address',
            'ctrl': 'bus_interface.input_side.ch0.payload.control',
            'data0': 'bus_interface.input_side.ch0.payload.data_word_0',
            'data1': 'bus_interface.input_side.ch0.payload.data_word_1'
        },
        'read_channel_a': {
            'valid': 'bus_interface.output_side.ch0.handshake.valid',
            'ready': 'bus_interface.output_side.ch0.handshake.ready',
            'addr': 'bus_interface.output_side.ch0.payload.address',
            'ctrl': 'bus_interface.output_side.ch0.payload.control',
            'data0': 'bus_interface.output_side.ch0.payload.data_word_0',
            'data1': 'bus_interface.output_side.ch0.payload.data_word_1'
        }
    }
    
    tb = GaxiMultiSigMapBufferTB(
        dut,
        wr_clk=dut.sys_clk,
        wr_rstn=dut.sys_rst_n,
        signal_map=hierarchical_map
    )
    await tb.initialize()
    
    # Test hierarchical signal access
    await tb.test_hierarchical_signal_access()
    await tb.test_mapped_concurrent_streams(num_packets=25)
```

## Advanced Features

### Signal Mapping Analytics

```python
def generate_signal_mapping_report(self):
    """Generate comprehensive signal mapping analytics"""
    
    report = []
    report.append("=" * 80)
    report.append("GAXI Signal Mapping Report")
    report.append("=" * 80)
    
    # Mapping summary
    total_channels = len(self.signal_map)
    total_signals = sum(len(signals) for signals in self.signal_map.values())
    
    report.append(f"Total Channels: {total_channels}")
    report.append(f"Total Mapped Signals: {total_signals}")
    report.append("")
    
    # Channel-by-channel breakdown
    for channel_name, channel_signals in self.signal_map.items():
        report.append(f"Channel: {channel_name}")
        report.append("-" * 40)
        
        for signal_type, signal_path in channel_signals.items():
            # Check signal existence
            signal_obj = self._find_signal(signal_path)
            status = "✓ Found" if signal_obj else "✗ Missing"
            
            report.append(f"  {signal_type:>8}: {signal_path:<30} {status}")
        
        report.append("")
    
    return "\n".join(report)

def validate_signal_mapping_completeness(self):
    """Validate that all required signals are mapped"""
    
    required_signals = ['valid', 'ready', 'addr', 'ctrl', 'data0', 'data1']
    missing_signals = []
    
    for channel_name, channel_signals in self.signal_map.items():
        for required_signal in required_signals:
            if required_signal not in channel_signals:
                missing_signals.append(f"{channel_name}.{required_signal}")
    
    if missing_signals:
        self.log.warning(f"Missing signal mappings: {', '.join(missing_signals)}")
        return False
    
    self.log.info("Signal mapping completeness validation PASSED")
    return True
```

The `gaxi_buffer_multi_sigmap.py` component provides comprehensive signal mapping capabilities, enabling flexible integration with diverse GAXI implementations while maintaining all the enhanced timing and verification features of the multi-signal testbench framework.