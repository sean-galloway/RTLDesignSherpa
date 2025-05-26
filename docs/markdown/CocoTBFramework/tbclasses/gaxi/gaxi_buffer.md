# GAXI Buffer Testbench

## Overview

The `GaxiBufferTB` class provides a base testbench for verifying AXI-style buffer implementations. It supports testing of GAXI (Generic AXI) interfaces with standard data fields, focusing on data integrity, proper handshaking, and timing behavior. The testbench includes comprehensive error detection and reporting, configurable randomization, and support for both synchronous and asynchronous designs.

## Class Definition

```python
class GaxiBufferTB(TBBase):
    """AXI style skid buffer Testbench using modular GAXI components"""

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
        
        # Gather the settings from the environment variables
        self.TEST_DEPTH = self.convert_to_int(os.environ.get('TEST_DEPTH', '0'))
        self.TEST_WIDTH = self.convert_to_int(os.environ.get('TEST_WIDTH', '0'))
        self.TEST_MODE = os.environ.get('TEST_MODE', 'skid')
        self.TEST_CLK_WR = self.convert_to_int(os.environ.get('TEST_CLK_WR', '10'))
        self.TEST_CLK_RD = self.convert_to_int(os.environ.get('TEST_CLK_RD', '10'))
```

## Key Features

- Support for AXI-style skid buffer and FIFO testing
- Parameterized data width and buffer depth
- Flexible timing controls via randomization profiles
- Comprehensive data integrity verification
- Detailed error reporting
- Support for both synchronous and asynchronous designs
- Monitor integration for transaction tracking
- Standard field mode operation

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
    self.rd_rstn.value = 0
    await self.clear_interface()

async def deassert_reset(self):
    """Deassert reset"""
    self.wr_rstn.value = 1
    self.rd_rstn.value = 1
    self.log.info("Reset complete.")
```

### compare_packets

Compares packets captured by write and read monitors to verify data integrity.

```python
def compare_packets(self, msg, expected_count):
    """
    Compare packets captured by wr_monitor and rd_monitor.
    Logs any mismatches without stopping the test and updates self.total_errors.
    
    Args:
        msg: Message for error reporting
        expected_count: Expected number of packets
    """
    # Check packet counts
    wr_mon_count = len(self.wr_monitor.observed_queue)
    rd_mon_count = len(self.rd_monitor.observed_queue)

    # Verify packet counts match expected count
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
            self.total_errors += 1
```

### simple_incremental_loops

Tests the buffer with incrementing data patterns.

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
    self.log.info(f'simple_incremental_loops({count=}, {delay_key=}, {delay_clks_after=}')
    self.write_master.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['write']))
    self.read_slave.set_randomizer(FlexRandomizer(RANDOMIZER_CONFIGS[delay_key]['read']))

    # Reset and prepare for test
    self.assert_reset()
    await self.wait_clocks(self.wr_clk_name, 10)
    self.deassert_reset()
    await self.wait_clocks(self.wr_clk_name, 10)

    # Send packets with incrementing data
    for i in range(count):
        # Create packet with data
        data = i & self.MAX_DATA # mask the data so we don't overflow
        packet = GAXIPacket(self.field_config)
        packet.data = data

        # Queue the packet - this doesn't wait for transmission
        await self.write_master.send(packet)

    # Wait until all is transferred
    while self.write_master.transfer_busy:
        await self.wait_clocks(self.wr_clk_name, 1)

    # Wait for data to be read
    await self.wait_clocks(self.wr_clk_name, delay_clks_after*50)
    while len(self.rd_monitor._recvQ) < count:
        await self.wait_clocks(self.wr_clk_name, 1)
    await self.wait_clocks(self.wr_clk_name, delay_clks_after)

    # Verify data integrity
    self.compare_packets("Simple Incremental Loops", count)

    assert self.total_errors == 0, f'Simple Incremental Loops found {self.total_errors} Errors'
```

## Component Setup

The testbench creates a comprehensive verification environment:

```python
# Define field configuration for skid buffer packets
self.field_config = FieldConfig.from_dict(FIELD_CONFIGS['standard'])
data_fld = self.field_config.get_field('data')
data_fld.active_bits= (self.DATA_WIDTH-1, 0)

# Create BFM components - add signal_map=None to explicitly use standard mode
self.write_master = GAXIMaster(
    dut, 'write_master', '', self.wr_clk,
    field_config=self.field_config,
    timeout_cycles=self.TIMEOUT_CYCLES,
    signal_map=None,  # Explicitly specify standard mode
    log=self.log,
)

self.read_slave = GAXISlave(
    dut, 'read_slave', '', self.rd_clk,
    mode=self.TEST_MODE,
    field_config=self.field_config,
    timeout_cycles=self.TIMEOUT_CYCLES,
    signal_map=None,  # Explicitly specify standard mode
    log=self.log
)

self.wr_monitor = GAXIMonitor(
    dut, 'Write monitor', '', self.wr_clk,
    field_config=self.field_config,
    is_slave=False,
    signal_map=None,  # Explicitly specify standard mode
    log=self.log
)

self.rd_monitor = GAXIMonitor(
    dut, 'Read monitor', '', self.rd_clk,
    mode=self.TEST_MODE,
    field_config=self.field_config,
    is_slave=True,
    signal_map=None,  # Explicitly specify standard mode
    log=self.log
)
```

## Error Reporting

The testbench provides detailed error reporting:

```python
if wr_mon_count != rd_mon_count:
    self.log.error(
        f"Packet count mismatch: "
        f"{wr_mon_count} sent vs "
        f"{rd_mon_count} received"
    )
    self.total_errors += 1

# ...

if wr_pkt != rd_pkt:
    self.log.error(
        f"{msg}: Packet mismatch – WR: {wr_pkt.formatted(compact=True)} "
        f"vs RD: {rd_pkt.formatted(compact=True)}"
    )
    self.total_errors += 1
```

## Example Usage

Basic usage of the GAXI buffer testbench:

```python
from CocoTBFramework.tbclasses.gaxi.gaxi_buffer import GaxiBufferTB

@cocotb.test()
async def test_gaxi_buffer(dut):
    # Set environment variables
    os.environ['TEST_DEPTH'] = '16'
    os.environ['TEST_WIDTH'] = '32'
    os.environ['TEST_MODE'] = 'skid'
    
    # Create testbench
    tb = GaxiBufferTB(
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
    
    # Check results
    assert tb.total_errors == 0, f"Test failed with {tb.total_errors} errors"
```

Using different timing profiles:

```python
# Test with fast back-to-back transfers
await tb.simple_incremental_loops(
    count=32,
    delay_key='backtoback',
    delay_clks_after=10
)

# Test with bursty traffic
await tb.simple_incremental_loops(
    count=32,
    delay_key='burst_pause',
    delay_clks_after=10
)

# Test with slow consumer
await tb.simple_incremental_loops(
    count=32,
    delay_key='slow_consumer',
    delay_clks_after=10
)
```

## Implementation Notes

- The testbench is configurable via environment variables
- Default signal mappings use standard mode (null signal map)
- Comprehensive error checking with detailed reporting
- Support for different delay profiles via randomization
- Complete verification environment with master, slave, and monitors

## Environment Variables

The testbench configuration is controlled by these variables:

- **TEST_DEPTH**: Buffer depth
- **TEST_WIDTH**: Width of data bus in bits
- **TEST_MODE**: Buffer mode ('skid', 'fifo_mux', etc.)
- **TEST_CLK_WR**: Write clock period
- **TEST_CLK_RD**: Read clock period

## See Also

- [GAXI Buffer Configs](gaxi_buffer_configs.md) - Configuration definitions
- [GAXI Buffer Field](gaxi_buffer_field.md) - Field-based GAXI testbench
- [GAXI Buffer Multi](gaxi_buffer_multi.md) - Multi-signal GAXI testbench

## Navigation

[↑ GAXI Testbenches Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
