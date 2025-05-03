# GAXI Buffer Testbench Examples

## Overview

The GAXI framework includes several testbench implementations that demonstrate how to use the GAXI components for testing various types of buffer designs. These testbenches are located in the `tbclasses/gaxi` directory and provide concrete examples of component integration and test scenarios.

This document covers the following testbench examples:

1. `gaxi_buffer.py` - Standard skid buffer testbench
2. `gaxi_buffer_field.py` - Field-based buffer testbench
3. `gaxi_buffer_multi.py` - Multi-signal buffer testbench
4. `gaxi_buffer_seq.py` - Sequence generator for buffer testing
5. `gaxi_data_collect_tb.py` - Data collection testbench

## Standard Skid Buffer Testbench (gaxi_buffer.py)

The `GaxiBufferTB` class in `gaxi_buffer.py` provides a testbench for validating standard AXI-style skid buffers with a single data bus.

### Key Features

- Tests skid buffers with single data field
- Supports configurable data width and depth
- Includes randomization of valid and ready signals
- Provides comprehensive verification with incrementing data patterns

### Class Definition

```python
class GaxiBufferTB(TBBase):
    def __init__(self, dut,
                 wr_clk=None, wr_rstn=None,
                 rd_clk=None, rd_rstn=None):
        # ...
```

### Key Methods

```python
async def clear_interface(self):
    """Clear the interface signals"""
    
async def assert_reset(self):
    """Assert reset"""
    
async def deassert_reset(self):
    """Deassert reset"""
    
def compare_packets(self, msg, expected_count):
    """Compare packets captured by wr_monitor and rd_monitor"""
    
async def simple_incremental_loops(self, count, delay_key, delay_clks_after):
    """Run simple incremental tests with different packet sizes"""
```

### Example Usage

```python
@cocotb.test()
async def test_skid_buffer(dut):
    """Test skid buffer with incrementing values"""
    # Create testbench
    tb = GaxiBufferTB(
        dut,
        wr_clk=dut.clk,
        wr_rstn=dut.rst_n
    )
    
    # Run test with incrementing values
    await tb.simple_incremental_loops(
        count=100,            # Number of transactions
        delay_key='fixed',    # Randomization profile
        delay_clks_after=10   # Additional delay after transfers
    )
```

## Field-Based Buffer Testbench (gaxi_buffer_field.py)

The `GaxiFieldBufferTB` class in `gaxi_buffer_field.py` tests buffer components that handle multiple fields packed into a single signal, such as address, control, and data fields.

### Key Features

- Tests buffers with multiple fields packed into signals
- Supports various field widths (address, control, data)
- Uses sequences for generating test patterns
- Provides various test sequences (walking ones, alternating patterns, etc.)

### Class Definition

```python
class GaxiFieldBufferTB(TBBase):
    """Testbench for multi-signal AXI components like axi_fifo_sync_field and axi_skid_buffer_field"""
    def __init__(self, dut,
                 wr_clk=None, wr_rstn=None,
                 rd_clk=None, rd_rstn=None):
        # ...
```

### Key Methods

```python
def create_sequences(self):
    """Create sequence generators for different test patterns"""
    
async def run_sequence_test(self, sequence, delay_key='fixed', delay_clks_after=5):
    """Run a test with the specified sequence"""
    
async def simple_incremental_loops(self, count, delay_key, delay_clks_after):
    """Run simple incremental tests with different packet sizes (legacy method)"""
```

### Example Usage

```python
@cocotb.test()
async def test_field_buffer(dut):
    """Test field buffer with various patterns"""
    # Create testbench
    tb = GaxiFieldBufferTB(
        dut,
        wr_clk=dut.clk,
        wr_rstn=dut.rst_n
    )
    
    # Run test with basic sequence
    await tb.run_sequence_test(
        sequence=tb.basic_sequence,
        delay_key='fixed',
        delay_clks_after=5
    )
    
    # Run test with walking ones sequence
    await tb.run_sequence_test(
        sequence=tb.walking_ones_sequence,
        delay_key='constrained',
        delay_clks_after=5
    )
    
    # Run test with comprehensive sequence
    await tb.run_sequence_test(
        sequence=tb.comprehensive_sequence,
        delay_key='burst_pause',
        delay_clks_after=10
    )
```

## Multi-Signal Buffer Testbench (gaxi_buffer_multi.py)

The `GaxiMultiBufferTB` class in `gaxi_buffer_multi.py` tests buffer components that use separate signals for each field, rather than packing fields into a single signal.

### Key Features

- Tests buffers with separate signals for each field
- Supports individual signal mapping for multi-signal mode
- Shares sequence generation with field-based testbench
- Handles different buffer operating modes (skid, fifo_mux, fifo_flop)

### Class Definition

```python
class GaxiMultiBufferTB(TBBase):
    """Testbench for multi-signal AXI components like axi_fifo_sync_multi and axi_skid_buffer_multi"""
    def __init__(self, dut,
                 wr_clk=None, wr_rstn=None,
                 rd_clk=None, rd_rstn=None):
        # ...
```

### Signal Mapping

```python
# Set up signal mappings for multi-signal mode
# Required signals (valid/ready) for master
master_signal_map = {
    'm2s_valid': 'i_wr_valid',
    's2m_ready': 'o_wr_ready'
}

# Optional signals (data fields) for master
master_optional_map = {
    'm2s_pkt_addr': 'i_wr_addr',
    'm2s_pkt_ctrl': 'i_wr_ctrl',
    'm2s_pkt_data0': 'i_wr_data0',
    'm2s_pkt_data1': 'i_wr_data1'
}

# Required signals (valid/ready) for slave
slave_signal_map = {
    'm2s_valid': 'o_rd_valid',
    's2m_ready': 'i_rd_ready'
}

# Optional signals (data fields) for slave
slave_optional_map = {
    'm2s_pkt_addr': 'o_rd_addr',
    'm2s_pkt_ctrl': 'o_rd_ctrl',
    'm2s_pkt_data0': 'o_rd_data0',
    'm2s_pkt_data1': 'o_rd_data1',
}
```

### Example Usage

```python
@cocotb.test()
async def test_multi_signal_buffer(dut):
    """Test multi-signal buffer with various patterns"""
    # Create testbench
    tb = GaxiMultiBufferTB(
        dut,
        wr_clk=dut.clk,
        wr_rstn=dut.rst_n
    )
    
    # Run stress test with multi-signal mode
    await tb.run_sequence_test(
        sequence=tb.stress_sequence,
        delay_key='constrained',
        delay_clks_after=10
    )
```

## Sequence Generator for Buffer Testing (gaxi_buffer_seq.py)

The `GAXIBufferSequence` class in `gaxi_buffer_seq.py` extends the base `GAXISequence` with specialized patterns for buffer testing.

### Key Features

- Generates sequences specific to buffer testing
- Supports multi-field packets (addr, ctrl, data0, data1)
- Provides various test patterns (incrementing, walking ones, alternating bits)
- Handles boundary value testing and overflow scenarios

### Class Definition

```python
class GAXIBufferSequence(GAXISequence):
    """
    Extended sequence generator for GAXI buffer tests with multi-field support.
    """
    def __init__(self, name, field_config, packet_class=GAXIPacket):
        # ...
```

### Key Methods

```python
def add_multi_field_transaction(self, addr=0, ctrl=0, data0=0, data1=0, delay=0):
    """Add a transaction with values for all fields"""
    
def add_incrementing_pattern(self, count, start_value=0, addr_step=1, ctrl_step=1,
                           data0_step=1, data1_step=1, delay=0):
    """Add transactions with incrementing values for all fields"""
    
def add_walking_ones_pattern(self, delay=0):
    """Add transactions with walking ones pattern across all fields"""
    
def add_field_test_pattern(self, delay=0):
    """Add test patterns that exercise all fields individually and together"""
    
def add_alternating_patterns(self, count, delay=0):
    """Add transactions with alternating bit patterns across fields"""
    
def add_random_data_pattern(self, count, delay=0):
    """Add transactions with random data in all fields"""
    
def add_boundary_values(self, delay=0):
    """Add transactions with boundary values for all fields"""
    
def add_overflow_test(self, delay=0):
    """Add transactions with values that exceed field widths to test masking"""
```

### Example Usage

```python
# Create a field configuration
field_config = FieldConfig()
field_config.add_field_dict('addr', {
    'bits': 32,
    'default': 0,
    'format': 'hex',
    'display_width': 2,
    'active_bits': (31, 0),
    'description': 'Address value'
})
field_config.add_field_dict('ctrl', {
    'bits': 8,
    'default': 0,
    'format': 'hex',
    'display_width': 2,
    'active_bits': (7, 0),
    'description': 'Control value'
})
field_config.add_field_dict('data0', {
    'bits': 32,
    'default': 0,
    'format': 'hex',
    'display_width': 4,
    'active_bits': (31, 0),
    'description': 'Data0 value'
})
field_config.add_field_dict('data1', {
    'bits': 32,
    'default': 0,
    'format': 'hex',
    'display_width': 4,
    'active_bits': (31, 0),
    'description': 'Data1 value'
})

# Create a buffer sequence
sequence = GAXIBufferSequence("buffer_test", field_config)

# Add test patterns
sequence.add_incrementing_pattern(count=10, delay=0)
sequence.add_walking_ones_pattern(delay=1)
sequence.add_field_test_pattern(delay=2)
sequence.add_boundary_values(delay=0)
sequence.add_overflow_test(delay=1)

# Generate packets
packets = sequence.generate_packets()
```

## Data Collection Testbench (gaxi_data_collect_tb.py)

The `DataCollectTB` class in `gaxi_data_collect_tb.py` provides a testbench for validating components that collect data from multiple input channels and combine them into output packets.

### Key Features

- Tests data collection from multiple input channels (A, B, C, D)
- Groups data from input channels into output packets
- Includes specialized scoreboard for data collection verification
- Supports weighted arbitration testing
- Provides stress testing capabilities

### Class Definition

```python
class DataCollectTB(TBBase):
    """
    Testbench for the data_collect module.
    Features:
    - 4 input channels (A, B, C, D) with GAXI Masters
    - 1 output channel (E) with GAXI Slave
    - Monitors for all channels
    - Scoreboard for verification
    - Support for weighted arbitration testing
    """
    def __init__(self, dut):
        # ...
```

### Key Methods

```python
def set_arbiter_weights(self, weight_a, weight_b, weight_c, weight_d):
    """Set the weights for the weighted round-robin arbiter"""
    
async def send_packets_on_channel(self, channel, count, id_value=None, base_data=0):
    """Send packets on a specific channel"""
    
async def run_simple_test(self, packets_per_channel=40, expected_outputs=10):
    """Run a simple test with equal packets on all channels"""
    
async def run_weighted_arbiter_test(self, weights_list=None):
    """Run a test with different arbiter weight configurations"""
    
async def run_stress_test(self, duration_clocks=10000):
    """Run a stress test with continuous data streams"""
```

### Example Usage

```python
@cocotb.test()
async def test_data_collect(dut):
    """Test data collection module with various scenarios"""
    # Create testbench
    tb = DataCollectTB(dut)
    
    # Run simple test with equal packets on all channels
    await tb.run_simple_test(
        packets_per_channel=100,
        expected_outputs=25  # Each output combines 4 inputs
    )
    
    # Run weighted arbiter test with different weights
    weights_list = [
        (8, 8, 0, 0),     # Equal A and B
        (4, 8, 12, 0),    # Varied weights
        (1, 2, 4, 8),     # Increasing weights
    ]
    await tb.run_weighted_arbiter_test(weights_list)
    
    # Run stress test
    await tb.run_stress_test(duration_clocks=5000)
```

## GAXI Enhancements (gaxi_enhancements.py)

The `gaxi_enhancements.py` file provides enhanced versions of the GAXI components with higher-level functionality:

### EnhancedGAXIMaster

This component wraps a basic GAXIMaster to provide:
- Direct memory read/write methods
- Automated address sequencing
- Command interface for coordinating with slave responses

```python
class EnhancedGAXIMaster:
    def __init__(self, master, memory_model=None, log=None):
        # ...
    
    async def read(self, addr):
        """Read data from specified address"""
    
    async def write(self, addr, data, strb=None):
        """Write data to specified address"""
    
    async def start_processor(self):
        """Start command processor task"""
    
    async def stop_processor(self):
        """Stop command processor task"""
```

### EnhancedGAXISlave

This component wraps a basic GAXISlave to provide:
- Automatic processing of incoming transactions
- Memory model integration
- Response queue management
- Custom processing callbacks

```python
class EnhancedGAXISlave:
    def __init__(self, slave, memory_model=None, log=None):
        # ...
    
    def set_read_callback(self, callback):
        """Set callback for custom read processing"""
    
    def set_write_callback(self, callback):
        """Set callback for custom write processing"""
    
    async def start_processor(self):
        """Start automatic transaction processor"""
    
    async def stop_processor(self):
        """Stop automatic transaction processor"""
```

## Enhanced GAXI Components Example

```python
@cocotb.test()
async def test_enhanced_components(dut):
    """Test enhanced GAXI components"""
    # Create base components
    field_config = FieldConfig()
    field_config.add_field_dict('addr', {'bits': 32})
    field_config.add_field_dict('data', {'bits': 32})
    
    memory_model = MemoryModel(num_lines=1024, bytes_per_line=4)
    
    master = GAXIMaster(dut, 'Master', '', dut.clk, field_config=field_config)
    slave = GAXISlave(dut, 'Slave', '', dut.clk, field_config=field_config)
    
    # Create enhanced components
    enhanced_master = EnhancedGAXIMaster(master, memory_model)
    enhanced_slave = EnhancedGAXISlave(slave, memory_model)
    
    # Start processors
    await enhanced_master.start_processor()
    await enhanced_slave.start_processor()
    
    # Perform direct memory operations
    await enhanced_master.write(0x1000, 0x12345678)
    data = await enhanced_master.read(0x1000)
    print(f"Read data: 0x{data:X}")
    
    # Set custom callbacks
    def read_callback(addr, packet):
        print(f"Custom read from address 0x{addr:X}")
        packet.data = 0xABCDEF01
    
    def write_callback(addr, data, packet):
        print(f"Custom write to address 0x{addr:X}: 0x{data:X}")
    
    enhanced_slave.set_read_callback(read_callback)
    enhanced_slave.set_write_callback(write_callback)
    
    # Stop processors
    await enhanced_master.stop_processor()
    await enhanced_slave.stop_processor()
```

## APB-Specific Command Handler Example

```python
@cocotb.test()
async def test_apb_command_handler(dut):
    """Test APB-specific command handler"""
    # Create field configurations
    cmd_field_config = FieldConfig()
    cmd_field_config.add_field_dict('addr', {'bits': 32})
    cmd_field_config.add_field_dict('data', {'bits': 32})
    
    rsp_field_config = FieldConfig()
    rsp_field_config.add_field_dict('data', {'bits': 32})
    rsp_field_config.add_field_dict('err', {'bits': 1})
    
    # Create master and slave components
    command_slave = GAXISlave(dut, 'CmdSlave', '', dut.clk, field_config=cmd_field_config)
    response_master = GAXIMaster(dut, 'RspMaster', '', dut.clk, field_config=rsp_field_config)
    
    # Create APB-specific command handler
    apb_handler = GAXICommandHandler_APBSlave(
        gaxi_master=response_master,
        gaxi_slave=command_slave,
        cmd_field_config=cmd_field_config,
        rsp_field_config=rsp_field_config
    )
    
    # Start the command handler
    await apb_handler.start()
    
    # The handler will automatically:
    # 1. Take packets from the command slave
    # 2. Create appropriate response packets
    # 3. Send them through the response master
    
    # Stop the command handler
    await apb_handler.stop()
```

## Tips and Best Practices

1. **Test Levels**: Start with simple tests and build up to more complex scenarios
2. **Sequence Reuse**: Create reusable sequence generators for common test patterns
3. **Buffer Types**: Select the appropriate testbench for your buffer type (standard/field/multi-signal)
4. **Randomization**: Use different randomization profiles to exercise edge cases
5. **Field Configuration**: Carefully define fields to match your design specifications
6. **Signal Mapping**: Provide explicit signal mappings for clear connections
7. **Enhanced Components**: Use enhanced components for higher-level functionality
8. **Command Handlers**: Use command handlers to coordinate complex transaction flows
9. **Data Collection**: Use the data collection testbench for modules that combine multiple inputs
10. **Weighted Arbitration**: Test arbitration behavior with different weight configurations

By leveraging these testbench examples, you can quickly develop comprehensive verification environments for AXI-style buffer components and other GAXI-compatible designs.
