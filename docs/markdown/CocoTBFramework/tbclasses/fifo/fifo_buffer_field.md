# FIFO Buffer Field Testbench

## Overview

The `FifoFieldBufferTB` class provides a testbench for verifying field-based FIFO buffer implementations. It extends the base FIFO testbench to support multi-field data formats, where the FIFO packet contains multiple fields (address, control, data) packed into a single data signal. This testbench includes comprehensive field-specific verification, dependency testing, and enhanced error reporting with field comparison.

## Class Definition

```python
class FifoFieldBufferTB(TBBase):
    """
    Testbench for multi-field FIFO components like fifo_sync_field and fifo_skid_buffer_field with enhanced error handling.
    """

    def __init__(self, dut, wr_clk=None, wr_rstn=None, rd_clk=None, rd_rstn=None):
        """
        Initialize the testbench with design under test.

        Args:
            dut: The cocotb design under test object
            wr_clk: Write clock signal
            wr_rstn: Write reset signal (active low)
            rd_clk: Read clock signal (same as wr_clk for sync FIFOs)
            rd_rstn: Read reset signal (same as wr_rstn for sync FIFOs)
        """
        super().__init__(dut)
        
        # Gather the settings from the Parameters
        self.TEST_DEPTH = self.convert_to_int(os.environ.get('TEST_DEPTH', '0'))
        self.TEST_ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '0'))
        self.TEST_CTRL_WIDTH = self.convert_to_int(os.environ.get('TEST_CTRL_WIDTH', '0'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '0'))
        self.TEST_MODE = os.environ.get('TEST_MODE', 'fifo_mux')
        self.TEST_KIND = os.environ.get('TEST_KIND', 'sync')
        self.TEST_CLK_WR = self.convert_to_int(os.environ.get('TEST_CLK_WR', '10'))
        self.TEST_CLK_RD = self.convert_to_int(os.environ.get('TEST_CLK_RD', '10'))
```

## Key Features

- Support for multi-field FIFO interfaces
- Field-specific data generation and verification
- Enhanced error reporting with field-by-field comparison
- Memory model integration with region tracking
- Command handler integration for coordinated testing
- Dependency testing between fields
- Transaction sequence generation and processing
- Detailed field-level error reporting

## Primary Methods

### clear_interface

Clears all interface signals to default values.

```python
async def clear_interface(self):
    """Clear the interface signals"""
    await self.write_master.reset_bus()
    await self.read_slave.reset_bus()
```

### assert_reset / deassert_reset

Controls reset signals for the testbench.

```python
async def assert_reset(self):
    """Assert reset"""
    self.wr_rstn.value = 0
    if self.rd_rstn != self.wr_rstn:
        self.rd_rstn.value = 0
    await self.clear_interface()

async def deassert_reset(self):
    """Deassert reset"""
    self.wr_rstn.value = 1
    if self.rd_rstn != self.wr_rstn:
        self.rd_rstn.value = 1
    self.log.info("Reset complete")
```

### compare_packets

Compares packets with enhanced field-by-field comparison.

```python
def compare_packets(self, msg, expected_count):
    """
    Compare packets captured by monitors.
    Logs any mismatches and updates self.total_errors.
    
    Args:
        msg: Message for error reporting
        expected_count: Expected number of packets
    """
    # Check packet counts
    # ...

    # Compare packets
    while self.wr_monitor.observed_queue and self.rd_monitor.observed_queue:
        wr_pkt = self.wr_monitor.observed_queue.popleft()
        rd_pkt = self.rd_monitor.observed_queue.popleft()

        # Compare the two packets
        if wr_pkt != rd_pkt:
            self.log.error(
                f"{msg}: Packet mismatch – WR: {wr_pkt.formatted(compact=True)} "
                f"vs RD: {rd_pkt.formatted(compact=True)}"
            )
            
            # Provide detailed field comparison
            all_fields = set(wr_pkt.get_all_field_names()) | set(rd_pkt.get_all_field_names())
            for field in all_fields:
                wr_val = getattr(wr_pkt, field, None)
                rd_val = getattr(rd_pkt, field, None)
                if wr_val != rd_val:
                    self.log.error(f"  Field '{field}' mismatch: write={wr_val}, read={rd_val}")
            
            self.total_errors += 1
```

### get_component_statistics

Collects comprehensive statistics including field region access.

```python
def get_component_statistics(self):
    """Get statistics from all components for analysis"""
    stats = {
        'write_master': self.write_master.get_stats(),
        'read_slave': self.read_slave.get_stats() if hasattr(self.read_slave, 'get_stats') else {},
        'write_monitor': self.wr_monitor.get_stats() if hasattr(self.wr_monitor, 'get_stats') else {},
        'read_monitor': self.rd_monitor.get_stats() if hasattr(self.rd_monitor, 'get_stats') else {},
        'memory_model': self.memory_model.get_stats() if hasattr(self.memory_model, 'get_stats') else {},
        'command_handler': self.command_handler.get_stats() if hasattr(self.command_handler, 'get_stats') else {}
    }
    
    # Get memory region statistics
    for region in ['addr_fields', 'ctrl_fields', 'data_fields']:
        region_stats = self.memory_model.get_region_access_stats(region)
        if region_stats:
            stats[f'memory_region_{region}'] = region_stats
            
    return stats
```

### simple_incremental_loops

Tests FIFO with incrementing multi-field data.

```python
async def simple_incremental_loops(self, count, delay_key, delay_clks_after):
    """
    Run simple incremental tests with different packet sizes.
    
    Args:
        count: Number of packets to send
        delay_key: Key for timing configuration
        delay_clks_after: Clock cycles to wait after test
    """
    # Choose the type of randomizer
    self.log.info(f'simple_incremental_loops({count=}, {delay_key=}, {delay_clks_after=})')
    self.write_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['write']))
    self.read_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['read']))

    # Reset and prepare for test
    await self.assert_reset()
    await self.wait_clocks(self.wr_clk_name, 10)
    await self.deassert_reset()
    await self.wait_clocks(self.wr_clk_name, 10)
    
    # Start the command handler
    await self.command_handler.start()

    # Send packets with incrementing field values
    for i in range(count):
        # Create packet with multiple fields
        addr = i & self.MAX_ADDR  # Mask address to avoid overflow
        ctrl = i & self.MAX_CTRL  # Mask control to avoid overflow
        data0 = i & self.MAX_DATA  # Mask data to avoid overflow
        data1 = (i * 2) & self.MAX_DATA  # Mask data to avoid overflow
        packet = FIFOPacket(self.field_config)
        packet.addr = addr
        packet.ctrl = ctrl
        packet.data0 = data0
        packet.data1 = data1

        # Queue the packet for transmission
        await self.write_master.send(packet)

    # Wait for transmission, verification, and cleanup
    # ...
```

### dependency_test

Tests transaction dependencies with complex sequences.

```python
async def dependency_test(self, count=10, delay_key='moderate'):
    """
    Test transaction dependencies with complex sequence.
    
    Args:
        count: Number of packets to send
        delay_key: Key for timing configuration
        
    Returns:
        True if test passed, False otherwise
    """
    from CocoTBFramework.components.fifo.fifo_sequence import FIFOSequence
    
    self.log.info(f"Running dependency test with {count} packets and {delay_key} delays")
    
    # Set randomizers for both components
    self.write_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['write']))
    self.read_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['read']))
    
    # Reset environment
    await self.assert_reset()
    await self.wait_clocks(self.wr_clk_name, 10)
    await self.deassert_reset()
    await self.wait_clocks(self.wr_clk_name, 10)
    
    # Start command handler
    await self.command_handler.start()
    
    # Create sequence with dependency chain
    sequence = FIFOSequence.create_dependency_chain(
        name="test_dependency_chain",
        count=count,
        data_start=0xA000,
        data_step=0x100,
        delay=1
    )
    
    # Set field configuration to match our testbench
    sequence.field_config = self.field_config
    
    # Process the sequence to generate packets
    self.log.info(f"Processing sequence with {count} packets")
    response_map = await self.command_handler.process_sequence(sequence)
    
    # Continue with verification and cleanup
    # ...
```

## Memory Model Configuration

The testbench includes an enhanced memory model with region tracking:

```python
# Create enhanced memory model
self.memory_model = EnhancedMemoryModel(
    num_lines=self.TEST_DEPTH,
    bytes_per_line=(self.AW + self.CW + 2*self.DW) // 8 or 1,
    log=self.log
)

# Define memory regions for better diagnostics
self.memory_model.define_region('addr_fields', 0, self.TEST_DEPTH // 4 - 1, 'Address fields')
self.memory_model.define_region('ctrl_fields', self.TEST_DEPTH // 4, self.TEST_DEPTH // 2 - 1, 'Control fields')
self.memory_model.define_region('data_fields', self.TEST_DEPTH // 2, self.TEST_DEPTH - 1, 'Data fields')
```

## Component Setup

The testbench creates a field-based verification environment:

```python
# Create field configuration
self.field_config = FieldConfig.from_dict(FIELD_CONFIGS['field'])
self.field_config.update_field_width('addr', self.AW)
self.field_config.update_field_width('ctrl', self.CW)
self.field_config.update_field_width('data0', self.DW)
self.field_config.update_field_width('data1', self.DW)

# Create BFM components - use field mode with appropriate signals
self.write_master = FIFOMaster(
    dut, 'write_master', '', self.wr_clk,
    field_config=self.field_config,
    field_mode=True,  # Enable field mode
    memory_model=self.memory_model,
    timeout_cycles=self.TIMEOUT_CYCLES,
    signal_map=master_signal_map,
    optional_signal_map=master_optional_map,
    log=self.log
)

self.read_slave = FIFOSlave(
    dut, 'read_slave', '', self.rd_clk,
    mode=self.TEST_MODE,
    field_config=self.field_config,
    field_mode=True,  # Enable field mode
    memory_model=self.memory_model,
    timeout_cycles=self.TIMEOUT_CYCLES,
    signal_map=slave_signal_map,
    optional_signal_map=slave_optional_map,
    log=self.log
)

# Set up monitors with field mode
self.wr_monitor = FIFOMonitor(...)
self.rd_monitor = FIFOMonitor(...)

# Create command handler to coordinate transactions
self.command_handler = FIFOCommandHandler(
    self.write_master,
    self.read_slave,
    memory_model=self.memory_model,
    log=self.log,
    fifo_capacity=self.TEST_DEPTH
)
```

## Example Usage

Basic usage of the field-based FIFO testbench:

```python
from CocoTBFramework.tbclasses.fifo.fifo_buffer_field import FifoFieldBufferTB

@cocotb.test()
async def test_fifo_field_buffer(dut):
    # Set environment variables
    os.environ['TEST_DEPTH'] = '16'
    os.environ['TEST_ADDR_WIDTH'] = '16'
    os.environ['TEST_CTRL_WIDTH'] = '8'
    os.environ['TEST_DATA_WIDTH'] = '32'
    os.environ['TEST_MODE'] = 'fifo_mux'
    os.environ['TEST_KIND'] = 'sync'
    
    # Create testbench
    tb = FifoFieldBufferTB(
        dut,
        wr_clk=dut.i_clk,
        wr_rstn=dut.i_rst_n,
        rd_clk=dut.i_clk,
        rd_rstn=dut.i_rst_n
    )
    
    # Run simple test
    await tb.simple_incremental_loops(
        count=32,
        delay_key='constrained',
        delay_clks_after=10
    )
    
    # Run dependency test
    await tb.dependency_test(
        count=20,
        delay_key='moderate'
    )
    
    # Check results
    assert tb.total_errors == 0, f"Test failed with {tb.total_errors} errors"
```

Using sequence-based testing:

```python
from CocoTBFramework.components.fifo.fifo_sequence import FIFOSequence

# Create a custom dependency test
@cocotb.test()
async def test_fifo_dependency(dut):
    # Create testbench
    tb = FifoFieldBufferTB(...)
    
    # Reset and prepare for test
    await tb.assert_reset()
    await tb.wait_clocks(tb.wr_clk_name, 10)
    await tb.deassert_reset()
    await tb.wait_clocks(tb.wr_clk_name, 10)
    
    # Start command handler
    await tb.command_handler.start()
    
    # Create custom sequence with field dependencies
    sequence = FIFOSequence(name="custom_dependency")
    sequence.field_config = tb.field_config
    
    # Add packets with dependencies
    for i in range(10):
        packet = FIFOPacket(tb.field_config)
        packet.addr = 0x1000 + i
        packet.ctrl = i % 4
        packet.data0 = 0xA000 + (i * 0x100)
        packet.data1 = 0xB000 + (i * 0x100)
        sequence.add_packet(packet)
    
    # Process sequence
    response_map = await tb.command_handler.process_sequence(sequence)
    
    # Verify responses
    for tx_id, response in response_map.items():
        assert response['status'] == 'completed', f"Transaction {tx_id} failed: {response}"
    
    # Stop command handler
    await tb.command_handler.stop()
    
    # Check component statistics
    stats = tb.get_component_statistics()
    print(f"Test Statistics: {stats}")
```

## Implementation Notes

- Extends the basic FIFO testbench for multi-field support
- Uses field_mode=True for all components
- Includes command handler for coordinated testing
- Supports field-specific verification and error reporting
- Includes memory regions for tracking different field accesses
- Provides detailed field comparison for mismatches
- Includes dependency testing between fields
- Integrated with sequence-based testing for complex scenarios

## Environment Variables

The testbench configuration is controlled by these variables:

- **TEST_DEPTH**: FIFO buffer depth
- **TEST_ADDR_WIDTH**: Width of address field in bits
- **TEST_CTRL_WIDTH**: Width of control field in bits
- **TEST_DATA_WIDTH**: Width of data fields in bits
- **TEST_MODE**: FIFO read mode ('fifo_mux' or 'fifo_flop')
- **TEST_KIND**: FIFO synchronization ('sync' or 'async')
- **TEST_CLK_WR**: Write clock period
- **TEST_CLK_RD**: Read clock period

## See Also

- [FIFO Buffer](fifo_buffer.md) - Standard FIFO testbench
- [FIFO Buffer Configs](fifo_buffer_configs.md) - Configuration definitions
- [FIFO Buffer Multi](fifo_buffer_multi.md) - Multi-signal FIFO testbench
- [FIFO Command Handler](../../components/fifo/fifo_command_handler.md) - Command processing
- [FIFO Sequence](../../components/fifo/fifo_sequence.md) - Sequence generation

## Navigation

[↑ FIFO Testbenches Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
