# FIFO Buffer Multi Testbench

## Overview

The `FifoMultiBufferTB` class provides a testbench for verifying FIFO buffer implementations with multi-signal interfaces. It extends the FIFO testbench capabilities to support designs where each field has its own separate signal, as opposed to fields being packed into a single data bus. This testbench includes protocol error testing, field-specific handling, and enhanced error detection.

## Class Definition

```python
class FifoMultiBufferTB(TBBase):
    """
    Testbench for multi-signal FIFO components like fifo_sync_multi and fifo_skid_buffer_multi with enhanced error detection.
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

- Support for multi-signal FIFO interfaces
- Separate signals for each data field
- Protocol error testing for violations
- Enhanced FIFO metadata tracking
- Buffer state verification
- Field-specific error reporting
- Command handler integration
- Support for various test sequence types

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
            
            # Provide detailed field comparison for debugging
            all_fields = set(wr_pkt.get_all_field_names()) | set(rd_pkt.get_all_field_names())
            for field in all_fields:
                wr_val = getattr(wr_pkt, field, None)
                rd_val = getattr(rd_pkt, field, None)
                if wr_val != rd_val:
                    self.log.error(f"  Field '{field}' mismatch: write={wr_val}, read={rd_val}")
            
            self.total_errors += 1
```

### get_component_statistics

Collects statistics from all components for analysis.

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
    return stats
```

### simple_incremental_loops

Tests FIFO with incrementing multi-field data on separate signals.

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
        # Create packet with multiple fields on separate signals
        addr = i & self.MAX_ADDR  # Mask address to avoid overflow
        ctrl = i & self.MAX_CTRL  # Mask control to avoid overflow
        data0 = i & self.MAX_DATA  # Mask data to avoid overflow
        data1 = (i * 2) & self.MAX_DATA  # Mask data to avoid overflow
        packet = FIFOPacket(self.field_config)
        packet.addr = addr
        packet.ctrl = ctrl
        packet.data0 = data0
        packet.data1 = data1
        
        # Set FIFO metadata for improved debugging
        packet.set_fifo_metadata(
            depth=min(i, self.TEST_DEPTH), 
            capacity=self.TEST_DEPTH
        )

        # Queue the packet for transmission
        await self.write_master.send(packet)

    # Wait for transmission, verification, and cleanup
    # ...
```

### run_sequence_test

Runs a test using predefined FIFO sequences.

```python
async def run_sequence_test(self, sequence_type='comprehensive', count=20):
    """
    Run a test using predefined FIFO sequences.
    
    Args:
        sequence_type: Type of sequence to run
        count: Number of packets to generate
        
    Returns:
        True if test passed, False otherwise
    """
    from CocoTBFramework.components.fifo.fifo_sequence import FIFOSequence
    
    self.log.info(f"Running {sequence_type} sequence test with {count} packets")
    
    # Reset the environment
    await self.assert_reset()
    await self.wait_clocks(self.wr_clk_name, 10)
    await self.deassert_reset()
    await self.wait_clocks(self.wr_clk_name, 10)
    
    # Start the command handler
    await self.command_handler.start()
    
    # Create the appropriate sequence
    if sequence_type == 'comprehensive':
        sequence = FIFOSequence.create_comprehensive_test(
            name="comprehensive_test",
            capacity=self.TEST_DEPTH,
            data_width=self.DW
        )
    elif sequence_type == 'stress':
        sequence = FIFOSequence.create_data_stress_test(
            name="stress_test",
            data_width=self.DW,
            delay=1
        )
    elif sequence_type == 'burst':
        sequence = FIFOSequence.create_burst_sequence(
            name="burst_test",
            count=count // 5,
            burst_size=5,
            pattern_type="increment"
        )
    elif sequence_type == 'capacity':
        sequence = FIFOSequence.create_fifo_capacity_test(
            name="capacity_test",
            capacity=self.TEST_DEPTH
        )
    else:
        self.log.error(f"Unknown sequence type: {sequence_type}")
        return False
        
    # Set field configuration to match our testbench
    sequence.field_config = self.field_config
    
    # Process sequence and verify results
    # ...
```

### protocol_error_test

Tests error detection features in the FIFO components.

```python
async def protocol_error_test(self):
    """
    Test error detection features in the FIFO components.
    
    Returns:
        True if test passed, False otherwise
    """
    self.log.info("Running protocol error test")
    
    # Set to faster randomizers for quicker testing
    self.write_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['fast']['write']))
    self.read_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS['fast']['read']))
    
    # Reset environment
    await self.assert_reset()
    await self.wait_clocks(self.wr_clk_name, 10)
    await self.deassert_reset()
    await self.wait_clocks(self.wr_clk_name, 10)
    
    # Start the command handler
    await self.command_handler.start()
    
    # Test field width violations
    self.log.info("Testing field width violations")
    
    # Create a packet with field values that exceed their bit widths
    packet_oversized = FIFOPacket(self.field_config)
    packet_oversized.addr = (1 << (self.AW + 2)) - 1  # Value exceeds AW bit width
    packet_oversized.ctrl = (1 << (self.CW + 4)) - 1  # Value exceeds CW bit width
    packet_oversized.data0 = (1 << (self.DW + 8)) - 1  # Value exceeds DW bit width
    packet_oversized.data1 = (1 << (self.DW + 16)) - 1  # Value exceeds DW bit width
    
    # Send the oversized packet and verify handling
    # ...
```

## Multi-Signal Configuration

The testbench uses multi-signal mode for separate field signals:

```python
# Set up signal mappings for multi-signal mode

# Optional signals (data fields) for master
master_optional_map = {
    'i_wr_pkt_addr': 'i_wr_addr',
    'i_wr_pkt_ctrl': 'i_wr_ctrl',
    'i_wr_pkt_data0': 'i_wr_data0',
    'i_wr_pkt_data1': 'i_wr_data1'
}

# Optional signals (data fields) for slave
slave_optional_map = {
    'o_rd_pkt_addr': 'o_rd_addr',
    'o_rd_pkt_ctrl': 'o_rd_ctrl',
    'o_rd_pkt_data0': 'o_rd_data0',
    'o_rd_pkt_data1': 'o_rd_data1',
}

# For fifo_mux mode, we also need to map to ow_rd_* signals
if self.TEST_MODE == 'fifo_mux':
    slave_optional_map['m2s_pkt_addr'] = 'ow_rd_addr'
    slave_optional_map['m2s_pkt_ctrl'] = 'ow_rd_ctrl'
    slave_optional_map['m2s_pkt_data0'] = 'ow_rd_data0'
    slave_optional_map['m2s_pkt_data1'] = 'ow_rd_data1'
```

## Component Setup

The testbench creates a multi-signal verification environment:

```python
# Create BFM components - use multi-signal mode with signal maps
self.write_master = FIFOMaster(
    dut, 'write_master', '', self.wr_clk,
    field_config=self.field_config,
    memory_model=self.memory_model,
    timeout_cycles=self.TIMEOUT_CYCLES,
    optional_signal_map=master_optional_map,
    log=self.log,
    multi_sig=True  # Enable multi-signal mode
)

self.read_slave = FIFOSlave(
    dut, 'read_slave', '', self.rd_clk,
    mode=self.TEST_MODE,
    field_config=self.field_config,
    memory_model=self.memory_model,
    timeout_cycles=self.TIMEOUT_CYCLES,
    optional_signal_map=slave_optional_map,
    log=self.log,
    multi_sig=True  # Enable multi-signal mode
)

# Set up monitors with multi-signal mode
self.wr_monitor = FIFOMonitor(...)
self.rd_monitor = FIFOMonitor(...)

# Create command handler to coordinate transactions
self.command_handler = FIFOCommandHandler(...)
```

## Example Usage

Basic usage of the multi-signal FIFO testbench:

```python
from CocoTBFramework.tbclasses.fifo.fifo_buffer_multi import FifoMultiBufferTB

@cocotb.test()
async def test_fifo_multi_buffer(dut):
    # Set environment variables
    os.environ['TEST_DEPTH'] = '16'
    os.environ['TEST_ADDR_WIDTH'] = '16'
    os.environ['TEST_CTRL_WIDTH'] = '8'
    os.environ['TEST_DATA_WIDTH'] = '32'
    os.environ['TEST_MODE'] = 'fifo_mux'
    os.environ['TEST_KIND'] = 'sync'
    
    # Create testbench
    tb = FifoMultiBufferTB(
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
    
    # Run sequence test
    await tb.run_sequence_test(
        sequence_type='comprehensive',
        count=20
    )
    
    # Test protocol error handling
    await tb.protocol_error_test()
    
    # Check results
    assert tb.total_errors == 0, f"Test failed with {tb.total_errors} errors"
```

Using different sequence types:

```python
# Run burst sequence test
await tb.run_sequence_test(
    sequence_type='burst',
    count=50
)

# Run stress test
await tb.run_sequence_test(
    sequence_type='stress',
    count=100
)

# Run capacity test
await tb.run_sequence_test(
    sequence_type='capacity',
    count=tb.TEST_DEPTH
)
```

## Implementation Notes

- Extends the basic FIFO testbench for multi-signal support
- Uses multi_sig=True for all components
- Each field has its own separate signal path
- Includes command handler for coordinated testing
- Supports field-specific verification and error reporting
- Includes FIFO metadata tracking for enhanced debugging
- Tests protocol violations with oversized field values
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
- [FIFO Buffer Field](fifo_buffer_field.md) - Field-based FIFO testbench
- [FIFO Command Handler](../../components/fifo/fifo_command_handler.md) - Command processing
- [FIFO Sequence](../../components/fifo/fifo_sequence.md) - Sequence generation

## Navigation

[↑ FIFO Testbenches Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
