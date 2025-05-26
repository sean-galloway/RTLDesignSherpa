# GAXI Multi-Signal Buffer Testbench

## Overview

The `GaxiMultiBufferTB` class provides a testbench for verifying AXI-style components with separate signals for different fields. Unlike the field-based testbench that uses a combined packet structure, this testbench is designed for testing components where each field (address, control, data) has its own dedicated signals. This approach enables testing of multi-signal AXI components like FIFOs and skid buffers with complex signal mappings.

## Class Definition

```python
class GaxiMultiBufferTB(TBBase):
    """Testbench for multi-signal AXI components like axi_fifo_sync_multi and axi_skid_buffer_multi"""

    def __init__(self, dut,
                 wr_clk=None, wr_rstn=None,
                 rd_clk=None, rd_rstn=None):
        """
        Initialize the testbench with design under test.

        Args:
            dut: The cocotb design under test object
            wr_clk: Write clock signal
            wr_rstn: Write reset signal (active low)
            rd_clk: Read clock signal (same as wr_clk for sync buffers)
            rd_rstn: Read reset signal (same as wr_rstn for sync buffers)
        """
        super().__init__(dut)

        # Get test parameters from environment
        self.TEST_DEPTH = self.convert_to_int(os.environ.get('TEST_DEPTH', '0'))
        self.TEST_ADDR_WIDTH = self.convert_to_int(os.environ.get('TEST_ADDR_WIDTH', '0'))
        self.TEST_CTRL_WIDTH = self.convert_to_int(os.environ.get('TEST_CTRL_WIDTH', '0'))
        self.TEST_DATA_WIDTH = self.convert_to_int(os.environ.get('TEST_DATA_WIDTH', '0'))
        self.TEST_MODE = os.environ.get('TEST_MODE', 'skid')
        self.TEST_CLK_WR = self.convert_to_int(os.environ.get('TEST_CLK_WR', '10'))
        self.TEST_CLK_RD = self.convert_to_int(os.environ.get('TEST_CLK_RD', '10'))
```

## Key Features

- Support for multi-signal AXI components with separate signals per field
- Explicit signal mapping for complex interfaces
- Parameterized field widths
- Integrated sequence generator for comprehensive testing
- Advanced test pattern generation
- Support for various test scenarios through sequence objects
- Comprehensive error detection and reporting
- Support for both synchronous and asynchronous designs

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

Compares packets captured by monitors to verify data integrity.

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
    wr_mon_count = len(self.wr_monitor.observed_queue)
    rd_mon_count = len(self.rd_monitor.observed_queue)

    # Verify packet counts match expected count
    if wr_mon_count != rd_mon_count:
        self.log.error(
            f"Packet count mismatch: "
            f"{wr_mon_count} sent vs "
            f"{rd_mon_count} received"
        )
        self.total_errors += 1

    if expected_count != wr_mon_count:
        self.log.error(
            f"Packet count mismatch on Write Monitor: "
            f"{wr_mon_count} sent vs "
            f"{expected_count} expected"
        )
        self.total_errors += 1

    if expected_count != rd_mon_count:
        self.log.error(
            f"Packet count mismatch on Read Monitor: "
            f"{rd_mon_count} received vs "
            f"{expected_count} expected"
        )
        self.total_errors += 1

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
            self.total_errors += 1
```

### run_sequence_test

Runs a test with a specified test sequence.

```python
async def run_sequence_test(self, sequence, delay_key='fixed', delay_clks_after=5):
    """
    Run a test with the specified sequence.

    Args:
        sequence: GAXIBufferSequence to use for the test
        delay_key: Key for the randomizer configuration to use
        delay_clks_after: Additional delay clocks after sending all packets
    """
    # Get randomizers
    if sequence.master_randomizer:
        self.write_master.set_randomizer(sequence.master_randomizer)
    else:
        self.write_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['write']))

    if sequence.slave_randomizer:
        self.read_slave.set_randomizer(sequence.slave_randomizer)
    else:
        self.read_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['read']))

    # Reset and prepare for test
    await self.assert_reset()
    await self.wait_clocks(self.wr_clk_name, 10)
    await self.deassert_reset()
    await self.wait_clocks(self.wr_clk_name, 10)

    # Generate the packets from the sequence
    packets = sequence.generate_packets()
    count = len(packets)

    self.log.info(f"Running sequence '{sequence.name}' with {count} packets")

    # Send all packets
    for packet in packets:
        await self.write_master.send(packet)

    # Wait for all packets to be transmitted
    while self.write_master.transfer_busy:
        await self.wait_clocks(self.wr_clk_name, 1)

    # Allow time for processing
    await self.wait_clocks(self.wr_clk_name, delay_clks_after*10)

    # Wait for all packets to be received
    timeout_counter = 0
    while len(self.rd_monitor.observed_queue) < count and timeout_counter < self.TIMEOUT_CYCLES:
        await self.wait_clocks(self.wr_clk_name, 1)
        timeout_counter += 1

    if timeout_counter >= self.TIMEOUT_CYCLES:
        self.log.error(f"Timeout waiting for packets! Only received {len(self.rd_monitor.observed_queue)} of {count}")

    # Additional delay for stable results
    await self.wait_clocks(self.wr_clk_name, delay_clks_after)

    # Compare the packets
    self.compare_packets(f"Sequence Test '{sequence.name}'", count)

    # Log results
    if self.total_errors == 0:
        self.log.info(f"Sequence Test '{sequence.name}' PASSED!")
    else:
        self.log.error(f"Sequence Test '{sequence.name}' FAILED with {self.total_errors} errors!")

    # Assert no errors
    assert self.total_errors == 0, f"Sequence Test '{sequence.name}' failed with {self.total_errors} errors"

    # Reset error counter for next test
    self.total_errors = 0
```

### simple_incremental_loops

Tests the buffer with incrementing data patterns.

```python
async def simple_incremental_loops(self, count, delay_key, delay_clks_after):
    """Run simple incremental tests with different packet sizes (legacy method)"""
    # Choose the type of randomizer
    self.log.info(f'simple_incremental_loops({count=}, {delay_key=}, {delay_clks_after=}')
    self.write_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['write']))
    self.read_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['read']))

    # Reset and prepare for test
    await self.assert_reset()
    await self.wait_clocks(self.wr_clk_name, 10)
    await self.deassert_reset()
    await self.wait_clocks(self.wr_clk_name, 10)

    # Send packets with multi-field data
    for i in range(count):
        # Create packet
        addr = i & self.MAX_ADDR  # Mask address to avoid overflow
        ctrl = i & self.MAX_CTRL  # Mask control to avoid overflow
        data0 = i & self.MAX_DATA  # Mask data to avoid overflow
        data1 = i*16 & self.MAX_DATA  # Mask data to avoid overflow
        packet = GAXIPacket(self.field_config)
        packet.addr=addr
        packet.ctrl=ctrl
        packet.data0=data0
        packet.data1=data1

        # Queue the packet for transmission
        await self.write_master.send(packet)

    # Wait for all packets to be transmitted
    while self.write_master.transfer_busy:
        await self.wait_clocks(self.wr_clk_name, 1)

    # Read data from the buffer
    await self.wait_clocks(self.wr_clk_name, delay_clks_after*50)

    # Wait for all packets to be received
    timeout_counter = 0
    while len(self.rd_monitor.observed_queue) < count and timeout_counter < self.TIMEOUT_CYCLES:
        await self.wait_clocks(self.wr_clk_name, 1)
        timeout_counter += 1

    if timeout_counter >= self.TIMEOUT_CYCLES:
        self.log.error(f"Timeout waiting for packets! Only received {len(self.rd_monitor.observed_queue)} of {count}")

    # Additional delay for stable results
    await self.wait_clocks(self.wr_clk_name, delay_clks_after)

    # Compare the packets
    self.compare_packets("Simple Incremental Loops", count)

    assert self.total_errors == 0, f'Simple Incremental Loops found {self.total_errors} Errors'
```

## Signal Mapping

The testbench uses explicit signal mapping for connecting to DUT signals:

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

# For fifo_mux mode, we also need to map to ow_rd_* signals
if self.TEST_MODE == 'fifo_mux':
    slave_optional_map['m2s_pkt_addr'] = 'ow_rd_addr'
    slave_optional_map['m2s_pkt_ctrl'] = 'ow_rd_ctrl'
    slave_optional_map['m2s_pkt_data0'] = 'ow_rd_data0'
    slave_optional_map['m2s_pkt_data1'] = 'ow_rd_data1'
```

## Component Setup

The testbench creates a comprehensive verification environment:

```python
# Create BFM components - use multi-signal mode with signal maps
self.write_master = GAXIMaster(
    dut, 'write_master', '', self.wr_clk,
    field_config=self.field_config,
    timeout_cycles=self.TIMEOUT_CYCLES,
    signal_map=master_signal_map,
    optional_signal_map=master_optional_map,
    log=self.log,
    multi_sig=True
)

self.read_slave = GAXISlave(
    dut, 'read_slave', '', self.rd_clk,
    mode=self.TEST_MODE,
    field_config=self.field_config,
    timeout_cycles=self.TIMEOUT_CYCLES,
    signal_map=slave_signal_map,
    optional_signal_map=slave_optional_map,
    log=self.log,
    multi_sig=True
)

# Set up monitors
self.wr_monitor = GAXIMonitor(
    dut, 'Write monitor', '', self.wr_clk,
    field_config=self.field_config,
    is_slave=False,
    signal_map=master_signal_map,
    optional_signal_map=master_optional_map,
    log=self.log,
    multi_sig=True
)

self.rd_monitor = GAXIMonitor(
    dut, 'Read monitor', '', self.rd_clk,
    mode=self.TEST_MODE,
    field_config=self.field_config,
    is_slave=True,
    signal_map=slave_signal_map,
    optional_signal_map=slave_optional_map,
    log=self.log,
    multi_sig=True
)
```

## Sequence Creation

Similar to the field-based testbench, the multi-signal testbench creates comprehensive test sequences:

```python
def create_sequences(self):
    """Create sequence generators for different test patterns"""
    # Create basic sequence with incrementing patterns
    self.basic_sequence = GAXIBufferSequence("basic_test", self.field_config)
    self.basic_sequence.add_incrementing_pattern(count=20, delay=0)

    # Create walking ones sequence
    self.walking_ones_sequence = GAXIBufferSequence("walking_ones", self.field_config)
    self.walking_ones_sequence.add_walking_ones_pattern(delay=1)

    # Create alternating patterns sequence
    self.alternating_sequence = GAXIBufferSequence("alternating", self.field_config)
    self.alternating_sequence.add_alternating_patterns(count=2, delay=0)

    # Create random data sequence
    self.random_sequence = GAXIBufferSequence("random_data", self.field_config)
    self.random_sequence.add_random_data_pattern(count=20, delay=1)

    # Create comprehensive test sequence
    self.comprehensive_sequence = GAXIBufferSequence("comprehensive_test", self.field_config)
    self.comprehensive_sequence.add_incrementing_pattern(10, delay=1)
    self.comprehensive_sequence.add_walking_ones_pattern(delay=1)
    self.comprehensive_sequence.add_field_test_pattern(delay=1)
    self.comprehensive_sequence.add_alternating_patterns(1, delay=1)
    self.comprehensive_sequence.add_boundary_values(delay=2)
    self.comprehensive_sequence.add_overflow_test(delay=2)
    self.comprehensive_sequence.add_random_data_pattern(10, delay=1)

    # Create burst test sequence with fast randomizers
    # ...

    # Create stress test sequence with varied patterns
    # ...
```

## Example Usage

Basic usage of the GAXI multi-signal buffer testbench:

```python
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer_multi import GaxiMultiBufferTB

@cocotb.test()
async def test_gaxi_multi_buffer(dut):
    # Set environment variables
    os.environ['TEST_DEPTH'] = '16'
    os.environ['TEST_ADDR_WIDTH'] = '32'
    os.environ['TEST_CTRL_WIDTH'] = '8'
    os.environ['TEST_DATA_WIDTH'] = '32'
    os.environ['TEST_MODE'] = 'skid'
    
    # Create testbench
    tb = GaxiMultiBufferTB(
        dut,
        wr_clk=dut.i_clk,
        wr_rstn=dut.i_rst_n,
        rd_clk=dut.i_clk,
        rd_rstn=dut.i_rst_n
    )
    
    # Run test with basic sequence
    await tb.run_sequence_test(
        tb.basic_sequence,
        delay_key='constrained',
        delay_clks_after=10
    )
    
    # Run test with comprehensive sequence
    await tb.run_sequence_test(
        tb.comprehensive_sequence,
        delay_key='constrained',
        delay_clks_after=10
    )
```

Testing with different timing configurations:

```python
# Test with back-to-back transfers
await tb.run_sequence_test(
    tb.burst_sequence,
    delay_key='backtoback',
    delay_clks_after=5
)

# Test with slow consumer
await tb.run_sequence_test(
    tb.basic_sequence,
    delay_key='slow_consumer',
    delay_clks_after=20
)

# Test with slow producer
await tb.run_sequence_test(
    tb.basic_sequence,
    delay_key='slow_producer',
    delay_clks_after=20
)
```

## Key Differences from GaxiFieldBufferTB

The main differences between this testbench and the field-based testbench are:

1. **Signal Mapping**: Explicit signal mapping for each field in the packet
2. **Multi-Signal Mode**: Uses `multi_sig=True` for all components
3. **Component Configuration**: Different approach to connecting to DUT signals
4. **FIFO Mux Support**: Special handling for fifo_mux mode with different output signals

## Implementation Notes

- The testbench uses multi-signal mode for GAXI components
- Each field has a dedicated signal in the DUT interface
- Signal mapping is explicitly defined for all connections
- Special handling for fifo_mux mode output signals
- Field widths are configurable via environment variables
- Comprehensive error checking with detailed reporting
- Reuses the same sequence generation framework as field-based testbench

## Environment Variables

The testbench configuration is controlled by these variables:

- **TEST_DEPTH**: Buffer depth
- **TEST_ADDR_WIDTH**: Width of address field in bits
- **TEST_CTRL_WIDTH**: Width of control field in bits
- **TEST_DATA_WIDTH**: Width of data fields in bits
- **TEST_MODE**: Buffer mode ('skid', 'fifo_mux', etc.)
- **TEST_CLK_WR**: Write clock period
- **TEST_CLK_RD**: Read clock period

## See Also

- [GAXI Buffer](gaxi_buffer.md) - Basic GAXI buffer testbench
- [GAXI Buffer Configs](gaxi_buffer_configs.md) - Configuration definitions
- [GAXI Buffer Field](gaxi_buffer_field.md) - Field-based GAXI testbench
- [GAXI Buffer Sequence](gaxi_buffer_seq.md) - Sequence generators for GAXI testing

## Navigation

[↑ GAXI Testbenches Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)