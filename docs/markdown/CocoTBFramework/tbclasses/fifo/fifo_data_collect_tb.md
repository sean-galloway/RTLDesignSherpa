# FIFO Data Collection Testbench

## Overview

The `DataCollectTB` class provides a specialized testbench for verifying data collection modules that use FIFO interfaces. These modules collect data from multiple input channels, group them into larger chunks, and output them on a single channel. The testbench includes custom scoreboarding for multi-channel data aggregation, arbiter monitoring, and comprehensive error detection.

## Class Definition

```python
class DataCollectTB(TBBase):
    """
    Testbench for data_collect module with enhanced error detection and memory model integration.
    
    Features:
    - 4 input channels (A, B, C, D) with FIFO Masters
    - 1 output channel (E) with FIFO Slave
    - Monitors for all channels
    - Scoreboard for verification
    - Support for weighted arbitration testing
    - Memory model integration
    - Enhanced error detection and reporting
    """

    def __init__(self, dut):
        """
        Initialize the testbench with design under test.

        Args:
            dut: The cocotb design under test object
        """
        super().__init__(dut)
        
        # Get test parameters from environment variables
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('DATA_WIDTH', '8'))
        self.ID_WIDTH = self.convert_to_int(os.environ.get('ID_WIDTH', '4'))
        self.OUTPUT_FIFO_DEPTH = self.convert_to_int(os.environ.get('OUTPUT_FIFO_DEPTH', '16'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
```

## Key Features

- Multiple input channels (A, B, C, D) with FIFO masters
- Output channel (E) with FIFO slave
- Specialized scoreboard for multi-channel data collection
- Channel-based data grouping and verification
- Weighted round-robin arbitration monitoring
- Configurable test levels and scenarios
- Comprehensive error detection and reporting
- Memory model integration
- Randomized and directed test capabilities

## Primary Classes

### DataCollectScoreboard

Special scoreboard for data collection module verification.

```python
class DataCollectScoreboard:
    """
    Specialized scoreboard for data_collect module with enhanced field validation and error detection.

    Features:
    - Separate queues for each input channel (A, B, C, D)
    - Groups data in 4-item chunks by channel
    - Compares output packets against expected grouped data
    - Checks for leftover data at end of test
    - Enhanced field validation and mask caching
    """

    def __init__(self, title, input_field_config, output_field_config, log=None):
        """Initialize the scoreboard"""
        # Initialize queues for each channel
        self.queue_a = deque()  # Channel A (ID: 0xAA)
        self.queue_b = deque()  # Channel B (ID: 0xBB)
        self.queue_c = deque()  # Channel C (ID: 0xCC)
        self.queue_d = deque()  # Channel D (ID: 0xDD)

        # Combined packet queues for each channel (after grouping 4 packets)
        self.combined_queue_a = deque()
        self.combined_queue_b = deque()
        self.combined_queue_c = deque()
        self.combined_queue_d = deque()

        # Queue for actual output packets
        self.actual_queue = deque()
```

### DataCollectTB

Main testbench class for data collection module.

```python
class DataCollectTB(TBBase):
    """
    Testbench for data_collect module with enhanced error detection and memory model integration.
    """

    def __init__(self, dut):
        """Initialize the testbench with the DUT"""
        super().__init__(dut)
        
        # Get test parameters from environment variables
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('DATA_WIDTH', '8'))
        self.ID_WIDTH = self.convert_to_int(os.environ.get('ID_WIDTH', '4'))
        self.OUTPUT_FIFO_DEPTH = self.convert_to_int(os.environ.get('OUTPUT_FIFO_DEPTH', '16'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
```

## Key Methods

### DataCollectScoreboard Methods

#### add_input_packet

Adds an input packet to the appropriate channel queue.

```python
def add_input_packet(self, packet):
    """
    Add an input packet to the appropriate queue based on ID.
    
    Args:
        packet: Input packet from a monitor
    """
    # Track statistics
    self.stats['packets_processed'] += 1
    
    # Determine which queue to add to based on ID
    packet_id = packet.id if hasattr(packet, 'id') else None

    # Determine which queue to add to based on ID
    if packet_id in [0xAA, 0xA]:
        self.queue_a.append(packet)
        # Check if we have 4 packets to combine
        if len(self.queue_a) >= 4:
            self._combine_packets('A')
    elif packet_id in [0xBB, 0xB]:
        # Similar handling for other channels...
```

#### _combine_packets

Combines 4 packets from a channel into a single output packet.

```python
def _combine_packets(self, channel):
    """
    Combine 4 packets from a channel into a single output packet with field validation.
    
    Args:
        channel: Channel identifier ('A', 'B', 'C', or 'D')
    """
    # Select the correct queue
    if channel == 'A':
        queue = self.queue_a
        combined_queue = self.combined_queue_a
        id_value = 0xAA
    elif channel == 'B':
        # Similar mapping for other channels...
        
    # Take 4 packets from the queue
    pkt0 = queue.popleft()
    pkt1 = queue.popleft()
    pkt2 = queue.popleft()
    pkt3 = queue.popleft()

    # Get data values from each packet
    data0 = pkt0.data if hasattr(pkt0, 'data') else 0
    data1 = pkt1.data if hasattr(pkt1, 'data') else 0
    data2 = pkt2.data if hasattr(pkt2, 'data') else 0
    data3 = pkt3.data if hasattr(pkt3, 'data') else 0
    
    # Mask values to ensure they're within field width
    # Create a combined output packet
    # Add to the combined queue
```

#### add_output_packet

Adds an output packet from the module and checks it against expected data.

```python
def add_output_packet(self, packet):
    """
    Add an output packet from the E monitor.
    
    Args:
        packet: Output packet from monitor E
    """
    self.actual_queue.append(packet)

    # Perform comparison immediately
    self._check_next_packet()
```

#### report

Generates a report and returns the number of errors.

```python
def report(self):
    """
    Generate a report and return the number of errors.
    
    Returns:
        Number of errors detected
    """
    # Check for any leftover data
    leftover_errors = self.check_remaining_data()
    total_errors = self.error_count + leftover_errors

    # Log summary
    self.log.info(f"Scoreboard report for {self.title}:")
    self.log.info(f"  Packets compared: {self.comparison_count}")
    self.log.info(f"  Data mismatches: {self.error_count}")
    self.log.info(f"  Leftover data errors: {leftover_errors}")
    self.log.info(f"  Total errors: {total_errors}")
    
    # Report details and return result
```

### DataCollectTB Methods

#### run_simple_test

Runs a simple test with equal packets on all channels.

```python
async def run_simple_test(self, packets_per_channel=40, expected_outputs=10):
    """
    Run a simple test with equal packets on all channels.
    
    Args:
        packets_per_channel: Number of packets to send on each channel
        expected_outputs: Expected number of output packets (for timeout calculation)
        
    Returns:
        True if test passed, False if failed
    """
    self.log.info(f"Starting simple test with {packets_per_channel} packets per channel")

    # Reset system
    await self.assert_reset()
    await self.wait_clocks('i_clk', 10)
    await self.deassert_reset()
    await self.wait_clocks('i_clk', 10)

    # Set equal weights for all channels
    self.set_arbiter_weights(8, 8, 8, 8)

    # Clear the scoreboard before starting
    self.scoreboard.clear()

    # Create input data streams with different IDs for each channel
    # Send packets, wait for completion, verify results
```

#### run_weighted_arbiter_test

Tests different arbiter weight configurations.

```python
async def run_weighted_arbiter_test(self, weights_list=None):
    """
    Run a test with different arbiter weight configurations.
    
    Args:
        weights_list: List of (weight_a, weight_b, weight_c, weight_d) tuples
                        If None, a default set of configurations is used
        
    Returns:
        True if all tests passed, False if any failed
    """
    # Default weights if none provided
    if weights_list is None:
        weights_list = [
            (15, 0, 0, 0),    # Channel A only
            (0, 15, 0, 0),    # Channel B only
            (0, 0, 15, 0),    # Channel C only
            (0, 0, 0, 15),    # Channel D only
            (8, 8, 0, 0),     # Equal A and B
            # More weight combinations...
        ]

    # Run test for each weight configuration
    # Reset, configure, send packets, verify for each configuration
```

#### run_stress_test

Runs a stress test with continuous data streams.

```python
async def run_stress_test(self, duration_clocks=10000):
    """
    Run a stress test with continuous data streams.
    
    Args:
        duration_clocks: Duration of the test in clock cycles
        
    Returns:
        True if test passed, False if failed
    """
    self.log.info(f"Starting stress test for {duration_clocks} clock cycles")

    # Reset system
    await self.assert_reset()
    await self.wait_clocks('i_clk', 10)
    await self.deassert_reset()
    await self.wait_clocks('i_clk', 10)

    # Clear the scoreboard
    self.scoreboard.clear()

    # Set randomizers for fast throughput
    self.set_master_randomizers('fast', 'fast', 'fast', 'fast')
    self.set_slave_randomizer('fast')

    # Set equal weights
    self.set_arbiter_weights(8, 8, 8, 8)

    # Start packet generation tasks
    # Run for specified duration
    # Collect and verify results
```

#### protocol_error_test

Tests error detection features.

```python
async def protocol_error_test(self):
    """
    Test error detection features.
    
    Returns:
        True if test passed, False otherwise
    """
    self.log.info("Starting protocol error test")
    
    # Reset system
    await self.assert_reset()
    await self.wait_clocks('i_clk', 10)
    await self.deassert_reset()
    await self.wait_clocks('i_clk', 10)
    
    # Clear the scoreboard
    self.scoreboard.clear()
    initial_errors = self.total_errors
    
    # Test error conditions
    # Create error scenarios and verify detection
```

## Component Setup

The testbench sets up a comprehensive verification environment:

```python
# Define field configuration for input channels (data+id)
self.input_field_config = FieldConfig()
self.input_field_config.add_field_dict('data', {
    'bits': self.DATA_WIDTH,
    'default': 0,
    'format': 'hex',
    'display_width': 2,
    'active_bits': (self.DATA_WIDTH-1, 0),
    'description': 'Data value'
})
self.input_field_config.add_field_dict('id', {
    'bits': self.ID_WIDTH,
    'default': 0,
    'format': 'hex',
    'display_width': 1,
    'active_bits': (self.ID_WIDTH-1, 0),
    'description': 'ID value'
})

# Define field configuration for output channel (id + 4 data fields)
self.output_field_config = FieldConfig()
self.output_field_config.add_field_dict('data0', {...})
self.output_field_config.add_field_dict('data1', {...})
self.output_field_config.add_field_dict('data2', {...})
self.output_field_config.add_field_dict('data3', {...})
self.output_field_config.add_field_dict('id', {...})

# Create memory models for each channel
# Create randomizers for masters with different configurations
# Define signal maps for masters/slaves/monitors
# Create FIFO masters for input channels
# Create FIFO slave for output channel
# Create monitors for inputs and output
# Create specialized scoreboard
```

## Arbiter Monitoring

The testbench includes weighted round-robin arbiter monitoring:

```python
# Initialize the arbiter monitors if applicable
try:
    from CocoTBFramework.components.arbiter_monitor import WeightedRoundRobinArbiterMonitor
    # Create Arbiter Monitor
    self.arbiter_monitor = WeightedRoundRobinArbiterMonitor(
        dut=self.dut_arb,
        title="WRR Arbiter Monitor",
        clock=self.dut_arb.i_clk,
        clock_period_ns=10,
        reset_n=self.dut_arb.i_rst_n,
        req_signal=self.dut_arb.i_req,
        gnt_valid_signal=self.dut_arb.ow_gnt_valid,
        gnt_signal=self.dut_arb.ow_gnt,
        gnt_id_signal=self.dut_arb.ow_gnt_id,
        gnt_ack_signal=self.dut_arb.i_gnt_ack if hasattr(self.dut, 'i_gnt_ack') else None,
        block_arb_signal=self.dut_arb.i_block_arb,
        max_thresh_signal=self.dut_arb.i_max_thresh,
        clients=self.dut_arb.CLIENTS,
        log=self.log
    )
except (ImportError, AttributeError):
    self.log.warning("WRR Monitor not available, skipping arbiter monitoring")
    self.arbiter_monitor = None
```

## Channel Data Handling

The scoreboard implements specialized channel data handling:

```python
# Handle channel A data
if packet_id in [0xAA, 0xA]:
    self.queue_a.append(packet)
    # Check if we have 4 packets to combine
    if len(self.queue_a) >= 4:
        self._combine_packets('A')
```

```python
# Combine 4 packets into a single output packet
def _combine_packets(self, channel):
    # Take 4 packets from the queue
    pkt0 = queue.popleft()
    pkt1 = queue.popleft()
    pkt2 = queue.popleft()
    pkt3 = queue.popleft()

    # Get data values from each packet
    data0 = pkt0.data if hasattr(pkt0, 'data') else 0
    data1 = pkt1.data if hasattr(pkt1, 'data') else 0
    data2 = pkt2.data if hasattr(pkt2, 'data') else 0
    data3 = pkt3.data if hasattr(pkt3, 'data') else 0
    
    # Mask values to ensure they're within field width
    data_mask = self._get_field_mask('data', self.input_field_config)
    data0 &= data_mask
    data1 &= data_mask
    data2 &= data_mask
    data3 &= data_mask
    
    # Create a combined output packet
    output_pkt = FIFOPacket(self.output_field_config)
    output_pkt.id = id_value
    output_pkt.data0 = data0
    output_pkt.data1 = data1
    output_pkt.data2 = data2
    output_pkt.data3 = data3

    # Add to the combined queue
    combined_queue.append(output_pkt)
```

## Example Usage

Basic usage of the data collect testbench:

```python
from CocoTBFramework.tbclasses.fifo.fifo_data_collect_tb import DataCollectTB

@cocotb.test()
async def test_data_collect(dut):
    # Set environment variables
    os.environ['DATA_WIDTH'] = '8'
    os.environ['ID_WIDTH'] = '4'
    os.environ['OUTPUT_FIFO_DEPTH'] = '16'
    
    # Create testbench
    tb = DataCollectTB(dut)
    
    # Run simple test
    await tb.run_simple_test(
        packets_per_channel=40,
        expected_outputs=10
    )
    
    # Run weighted test
    await tb.run_weighted_arbiter_test()
    
    # Run stress test
    await tb.run_stress_test(duration_clocks=5000)
    
    # Check results
    assert tb.total_errors == 0, f"Test failed with {tb.total_errors} errors"
```

Using custom weights for arbitration testing:

```python
# Test with custom weight configurations
weights_list = [
    (10, 5, 2, 1),   # Prioritize channel A
    (1, 10, 5, 2),   # Prioritize channel B
    (2, 1, 10, 5),   # Prioritize channel C
    (5, 2, 1, 10)    # Prioritize channel D
]

await tb.run_weighted_arbiter_test(weights_list=weights_list)
```

## Implementation Notes

- The testbench includes a specialized scoreboard for multi-channel data collection
- Each input channel has a dedicated master and queue in the scoreboard
- The scoreboard groups every 4 packets from a channel into a single output packet
- Channel isolation is verified through separate channel queues
- The arbiter monitor tracks channel selection based on weights
- Memory models are used for each channel for data storage and validation
- Error tracking includes detailed field-level validation
- The testbench supports different test levels with increasing complexity

## Environment Variables

The testbench configuration is controlled by these variables:

- **DATA_WIDTH**: Width of data fields in bits
- **ID_WIDTH**: Width of ID field in bits
- **OUTPUT_FIFO_DEPTH**: Depth of output FIFO buffer
- **SEED**: Random seed for reproducibility

## See Also

- [FIFO Buffer](fifo_buffer.md) - Standard FIFO testbench
- [FIFO Buffer Multi](fifo_buffer_multi.md) - Multi-signal FIFO testbench
- [Arbiter Monitor](../../components/arbiter_monitor.md) - Weighted round-robin arbiter monitoring

## Navigation

[↑ FIFO Testbenches Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
