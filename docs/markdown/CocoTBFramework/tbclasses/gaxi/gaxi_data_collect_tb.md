# GAXI Data Collection Testbench

## Overview

The `DataCollectTB` class provides a specialized testbench for verifying data collection modules that use GAXI interfaces. It's designed for testing components that collect data from multiple input channels, group it into larger packets, and output through a single channel. The testbench includes multiple GAXI masters for input, a GAXI slave for output, transaction monitoring, and a specialized scoreboard for data verification.

## Class Definition

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
        """Initialize the testbench with the DUT"""
        super().__init__(dut)

        # Get test parameters from environment variables
        self.DATA_WIDTH = self.convert_to_int(os.environ.get('DATA_WIDTH', '8'))
        self.ID_WIDTH = self.convert_to_int(os.environ.get('ID_WIDTH', '4'))
        self.OUTPUT_FIFO_DEPTH = self.convert_to_int(os.environ.get('OUTPUT_FIFO_DEPTH', '16'))
        self.SEED = self.convert_to_int(os.environ.get('SEED', '12345'))
```

## Key Features

- Support for multi-channel data collection testing
- Channel identification and routing verification
- Data grouping validation (4-to-1 packing)
- Weighted arbitration testing
- Comprehensive scoreboard for verification
- Multiple test types (simple, weighted, stress)
- Detailed error detection and reporting
- Configurable randomization for timing control
- Support for signal mapping and field configuration

## Primary Components

### DataCollectScoreboard

A specialized scoreboard for data_collect module verification.

```python
class DataCollectScoreboard:
    """
    Specialized scoreboard for data_collect module.

    Features:
    - Separate queues for each input channel (A, B, C, D)
    - Groups data in 4-item chunks by channel
    - Compares output packets against expected grouped data
    - Checks for leftover data at end of test
    """
    
    def __init__(self, title, input_field_config, output_field_config, log=None):
        """Initialize the scoreboard"""
        self.title = title
        # Convert to FieldConfig if received as dictionaries
        if isinstance(input_field_config, dict):
            self.input_field_config = FieldConfig.validate_and_create(input_field_config)
        else:
            self.input_field_config = input_field_config
            
        if isinstance(output_field_config, dict):
            self.output_field_config = FieldConfig.validate_and_create(output_field_config)
        else:
            self.output_field_config = output_field_config
```

### GAXI Masters for Input Channels

The testbench creates GAXI masters for each input channel:

```python
# Create GAXI masters for input channels
self.master_a = GAXIMaster(
    dut, 'Master A', '', self.clock,
    field_config=self.input_field_config,
    randomizer=self.master_a_randomizer,
    timeout_cycles=1000,
    signal_map=self.master_a_map,
    optional_signal_map=self.master_a_opt_map,
    multi_sig=True,
    log=self.log
)

# Similar setup for master_b, master_c, master_d
```

### GAXI Slave for Output Channel

The testbench creates a GAXI slave for the output channel:

```python
# Create GAXI slave for output channel
self.slave_e = GAXISlave(
    dut, 'Slave E', '', self.clock,
    field_config=self.output_field_config,
    randomizer=self.slave_e_randomizer,
    timeout_cycles=1000,
    signal_map=self.slave_e_map,
    optional_signal_map=self.slave_e_opt_map,
    multi_sig=False,
    field_mode=True,
    mode='skid',
    log=self.log
)
```

### Monitors for All Channels

The testbench includes monitors for all channels:

```python
# Create monitors for inputs
self.monitor_a = GAXIMonitor(
    dut, 'Monitor A', '', self.clock,
    field_config=self.input_field_config,
    is_slave=False,
    signal_map=self.master_a_map,
    optional_signal_map=self.master_a_opt_map,
    multi_sig=True,
    mode='skid',
    log=self.log
)

# Similar setup for monitor_b, monitor_c, monitor_d

# Create monitor for output
self.monitor_e = GAXIMonitor(
    dut, 'Monitor E', '', self.clock,
    field_config=self.output_field_config,
    is_slave=True,
    signal_map=self.slave_e_map,
    optional_signal_map=self.slave_e_opt_map,
    mode='skid',
    field_mode=True,
    multi_sig=False,
    log=self.log
)
```

## Primary Methods

### assert_reset / deassert_reset

Controls reset signals for the testbench.

```python
async def assert_reset(self):
    """Assert the reset signal"""
    self.reset_n.value = 0

    # Reset masters and slave
    await self.master_a.reset_bus()
    await self.master_b.reset_bus()
    await self.master_c.reset_bus()
    await self.master_d.reset_bus()
    await self.slave_e.reset_bus()

async def deassert_reset(self):
    """Deassert the reset signal"""
    self.reset_n.value = 1
    self.log.info("Reset deasserted")
```

### set_arbiter_weights

Sets the weights for the weighted round-robin arbiter.

```python
def set_arbiter_weights(self, weight_a, weight_b, weight_c, weight_d):
    """Set the weights for the weighted round-robin arbiter"""
    # Validate weights are within 0-15 range
    for name, weight in [('A', weight_a), ('B', weight_b), ('C', weight_c), ('D', weight_d)]:
        if weight < 0 or weight > 15:
            self.log.error(f"Invalid weight for channel {name}: {weight}. Must be 0-15.")
            return

    # Set the weights
    self.dut.i_weight_a.value = weight_a
    self.dut.i_weight_b.value = weight_b
    self.dut.i_weight_c.value = weight_c
    self.dut.i_weight_d.value = weight_d

    # Log the configuration
    self.log.info(f"Arbiter weights set: A={weight_a}, B={weight_b}, C={weight_c}, D={weight_d}")

    # Store the configuration for later analysis
    self.weight_configs.append((weight_a, weight_b, weight_c, weight_d))
```

### send_packets_on_channel

Sends packets on a specific channel.

```python
async def send_packets_on_channel(self, channel, count, id_value=None, base_data=0):
    """
    Send packets on a specific channel

    Args:
        channel: Channel to send on ('A', 'B', 'C', or 'D')
        count: Number of packets to send
        id_value: ID value to use (None for channel default)
        base_data: Base value for data (incremented for each packet)

    Returns:
        List of sent packets
    """
    # Choose the correct master and default ID
    if channel == 'A':
        master = self.master_a
        default_id = 0xAA
    elif channel == 'B':
        master = self.master_b
        default_id = 0xBB
    elif channel == 'C':
        master = self.master_c
        default_id = 0xCC
    elif channel == 'D':
        master = self.master_d
        default_id = 0xDD
    else:
        self.log.error(f"Unknown channel: {channel}")
        return []

    # Use provided ID or default
    if id_value is None:
        id_value = default_id

    # Create and send packets
    sent_packets = []
    for i in range(count):
        # Create packet
        pkt = GAXIPacket(self.input_field_config)
        pkt.id = id_value
        pkt.data = (base_data + i) & ((1 << self.DATA_WIDTH) - 1)  # Mask to WIDTH bits

        # Send packet
        await master.send(pkt)

        # Store packet for verification
        sent_packets.append(pkt)

        # Log every N packets
        if (i + 1) % 20 == 0 or i == 0 or i == count - 1:
            self.log.info(f"Sent {i+1}/{count} packets on channel {channel}")

    return sent_packets
```

### wait_for_expected_outputs

Waits until the expected number of outputs have been received or timeout.

```python
async def wait_for_expected_outputs(self, expected_count, timeout_clocks=5000):
    """
    Wait until the expected number of outputs have been received or timeout

    Args:
        expected_count: Expected number of output packets
        timeout_clocks: Maximum number of clock cycles to wait

    Returns:
        True if all expected outputs were received, False if timeout
    """
    count = 0
    while len(self.monitor_e.observed_queue) < expected_count and count < timeout_clocks:
        await self.wait_clocks('i_axi_aclk', 1)
        count += 1

        # Status updates every 200 clocks
        if count % 200 == 0:
            self.log.info(f"Waiting for outputs: {len(self.monitor_e.observed_queue)}/{expected_count} received")

    received = len(self.monitor_e.observed_queue)
    if received < expected_count:
        self.log.warning(f"Timeout waiting for outputs: {received}/{expected_count} received")
        return False

    self.log.info(f"All expected outputs received: {received}/{expected_count}")
    return True
```

## Test Methods

### run_simple_test

Runs a simple test with equal packets on all channels.

```python
async def run_simple_test(self, packets_per_channel=40, expected_outputs=10):
    """
    Run a simple test with equal packets on all channels

    Args:
        packets_per_channel: Number of packets to send on each channel
        expected_outputs: Expected number of output packets (for timeout calculation)

    Returns:
        True if test passed, False if failed
    """
    self.log.info(f"Starting simple test with {packets_per_channel} packets per channel")

    # Reset system
    await self.assert_reset()
    await self.wait_clocks('i_axi_aclk', 10)
    await self.deassert_reset()
    await self.wait_clocks('i_axi_aclk', 10)

    # Set equal weights for all channels
    self.set_arbiter_weights(8, 8, 8, 8)

    # Clear the scoreboard before starting
    self.scoreboard.clear()

    # Create input data streams with different IDs for each channel
    send_tasks = [
        cocotb.start_soon(
            self.send_packets_on_channel(
                'A', packets_per_channel, id_value=0xAA, base_data=0x100
            )
        )
    ]

    send_tasks.append(cocotb.start_soon(
        self.send_packets_on_channel('B', packets_per_channel, id_value=0xBB, base_data=0x200)
    ))
    send_tasks.append(cocotb.start_soon(
        self.send_packets_on_channel('C', packets_per_channel, id_value=0xCC, base_data=0x300)
    ))
    send_tasks.append(cocotb.start_soon(
        self.send_packets_on_channel('D', packets_per_channel, id_value=0xDD, base_data=0x400)
    ))

    # Wait for all sending tasks to complete and add packets to scoreboard
    for task in send_tasks:
        sent_packets_channel = await task
        # Add all packets to the scoreboard
        for pkt in sent_packets_channel:
            self.scoreboard.add_input_packet(pkt)

    # Wait for masters to finish transmitting
    await self.wait_for_all_masters_idle()
    self.log.info("All masters finished sending")

    # Calculate expected number of output packets (each channel produces packets_per_channel/4 outputs)
    total_expected_outputs = (packets_per_channel * 4) // 4

    # Wait for expected outputs
    await self.wait_for_expected_outputs(total_expected_outputs)

    # Add received packets to scoreboard
    self.add_received_packets_to_scoreboard()

    # Wait a bit to ensure all packets have been processed
    await self.wait_clocks('i_axi_aclk', 100)

    # Check scoreboard
    errors = self.check_scoreboard()

    return errors == 0
```

### run_weighted_arbiter_test

Runs a test with different arbiter weight configurations.

```python
async def run_weighted_arbiter_test(self, weights_list=None):
    """
    Run a test with different arbiter weight configurations

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
            (0, 8, 8, 0),     # Equal B and C
            (0, 0, 8, 8),     # Equal C and D
            (8, 0, 0, 8),     # Equal A and D
            (4, 8, 12, 0),    # Varied weights
            (1, 2, 4, 8),     # Increasing weights
        ]

    all_passed = True

    for i, weights in enumerate(weights_list):
        self.log.info(f"Starting weighted test {i+1}/{len(weights_list)} with weights: {weights}")

        # Reset system
        await self.assert_reset()
        await self.wait_clocks('i_axi_aclk', 10)
        await self.deassert_reset()
        await self.wait_clocks('i_axi_aclk', 10)

        # Set weights
        weight_a, weight_b, weight_c, weight_d = weights
        self.set_arbiter_weights(weight_a, weight_b, weight_c, weight_d)

        # Clear scoreboard
        self.scoreboard.clear()

        # Calculate packets per channel based on weights
        total_weight = max(1, weight_a + weight_b + weight_c + weight_d)
        base_count = 20  # Base number of packets per weight unit

        packets_a = 0 if weight_a == 0 else base_count * weight_a
        packets_b = 0 if weight_b == 0 else base_count * weight_b
        packets_c = 0 if weight_c == 0 else base_count * weight_c
        packets_d = 0 if weight_d == 0 else base_count * weight_d

        # Make sure packet counts are multiples of 4 for clean testing
        packets_a = (packets_a // 4) * 4
        packets_b = (packets_b // 4) * 4
        packets_c = (packets_c // 4) * 4
        packets_d = (packets_d // 4) * 4

        # Estimate expected output count (total packets / 4)
        expected_outputs = (packets_a + packets_b + packets_c + packets_d) // 4

        # Send packets concurrently
        send_tasks = []
        if packets_a > 0:
            send_tasks.append(cocotb.start_soon(
                self.send_packets_on_channel('A', packets_a, id_value=0xAA, base_data=0x100 + i*0x1000)
            ))

        # Similar tasks for channels B, C, and D
        # ...

        # Wait for all tasks to complete and add packets to scoreboard
        # ...

        # Wait for expected outputs
        # ...

        # Check scoreboard for errors
        errors = self.check_scoreboard()
        if errors > 0:
            self.log.error(f"Test {i+1}/{len(weights_list)} failed: {errors} scoreboard errors")
            all_passed = False
        else:
            self.log.info(f"Test {i+1}/{len(weights_list)} passed")

    return all_passed
```

### run_stress_test

Runs a stress test with continuous data streams.

```python
async def run_stress_test(self, duration_clocks=10000):
    """
    Run a stress test with continuous data streams

    Args:
        duration_clocks: Duration of the test in clock cycles

    Returns:
        True if test passed, False if failed
    """
    self.log.info(f"Starting stress test for {duration_clocks} clock cycles")

    # Reset system
    await self.assert_reset()
    await self.wait_clocks('i_axi_aclk', 10)
    await self.deassert_reset()
    await self.wait_clocks('i_axi_aclk', 10)

    # Clear the scoreboard
    self.scoreboard.clear()

    # Set randomizers for fast throughput
    self.set_master_randomizers('fast', 'fast', 'fast', 'fast')
    self.set_slave_randomizer('fast')

    # Set equal weights
    self.set_arbiter_weights(8, 8, 8, 8)

    # Start packet generation tasks - use multiples of 4 for clean testing
    task_a = cocotb.start_soon(self.send_packets_on_channel('A', 500, id_value=0xAA, base_data=0x100))
    task_b = cocotb.start_soon(self.send_packets_on_channel('B', 500, id_value=0xBB, base_data=0x200))
    task_c = cocotb.start_soon(self.send_packets_on_channel('C', 500, id_value=0xCC, base_data=0x300))
    task_d = cocotb.start_soon(self.send_packets_on_channel('D', 500, id_value=0xDD, base_data=0x400))

    # Wait for specified duration
    await self.wait_clocks('i_axi_aclk', duration_clocks)

    # Wait for tasks to complete
    sent_a = await task_a
    sent_b = await task_b
    sent_c = await task_c
    sent_d = await task_d

    # Add all sent packets to the scoreboard
    for pkt in sent_a:
        self.scoreboard.add_input_packet(pkt)
    for pkt in sent_b:
        self.scoreboard.add_input_packet(pkt)
    for pkt in sent_c:
        self.scoreboard.add_input_packet(pkt)
    for pkt in sent_d:
        self.scoreboard.add_input_packet(pkt)

    # Wait for masters to finish transmitting
    await self.wait_for_all_masters_idle()

    # Allow time for all packets to be processed
    await self.wait_clocks('i_axi_aclk', 500)

    # Add received packets to scoreboard
    self.add_received_packets_to_scoreboard()

    # Check the scoreboard
    errors = self.check_scoreboard()

    return errors == 0
```

## Scoreboard Methods

### add_input_packet

Adds an input packet to the appropriate queue based on ID.

```python
def add_input_packet(self, packet):
    """
    Add an input packet to the appropriate queue based on ID

    Args:
        packet: Input packet from a monitor
    """
    # Determine which queue to add to based on ID
    packet_id = packet.id if hasattr(packet, 'id') else None

    # Determine which queue to add to based on ID
    if packet_id in [0xAA, 0xA]:
        self.queue_a.append(packet)
        # Check if we have 4 packets to combine
        if len(self.queue_a) >= 4:
            self._combine_packets('A')
    elif packet_id in [0xBB, 0xB]:
        self.queue_b.append(packet)
        if len(self.queue_b) >= 4:
            self._combine_packets('B')
    elif packet_id in [0xCC, 0xC]:
        self.queue_c.append(packet)
        if len(self.queue_c) >= 4:
            self._combine_packets('C')
    elif packet_id in [0xDD, 0xD]:
        self.queue_d.append(packet)
        if len(self.queue_d) >= 4:
            self._combine_packets('D')
    else:
        self.log.warning(f"Received packet with unknown ID: 0x{packet_id:X}")
```

### _combine_packets

Combines 4 packets from a channel into a single output packet.

```python
def _combine_packets(self, channel):
    """
    Combine 4 packets from a channel into a single output packet

    Args:
        channel: Channel identifier ('A', 'B', 'C', or 'D')
    """
    # Select the correct queue
    if channel == 'A':
        queue = self.queue_a
        combined_queue = self.combined_queue_a
        id_value = 0xAA
    elif channel == 'B':
        queue = self.queue_b
        combined_queue = self.combined_queue_b
        id_value = 0xBB
    elif channel == 'C':
        queue = self.queue_c
        combined_queue = self.combined_queue_c
        id_value = 0xCC
    elif channel == 'D':
        queue = self.queue_d
        combined_queue = self.combined_queue_d
        id_value = 0xDD
    else:
        self.log.error(f"Unknown channel: {channel}")
        return

    # Ensure we have at least 4 packets
    if len(queue) < 4:
        return

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
    
    # Create a combined output packet
    output_pkt = GAXIPacket(self.output_field_config)
    output_pkt.id = id_value
    output_pkt.data0 = data0
    output_pkt.data1 = data1
    output_pkt.data2 = data2
    output_pkt.data3 = data3

    # Add to the combined queue
    combined_queue.append(output_pkt)
```

### add_output_packet / _check_next_packet

Adds an output packet and performs verification.

```python
def add_output_packet(self, packet):
    """
    Add an output packet from the E monitor

    Args:
        packet: Output packet from monitor E
    """
    self.actual_queue.append(packet)

    # Perform comparison immediately
    self._check_next_packet()

def _check_next_packet(self):
    """Check the next output packet against expected data"""
    if not self.actual_queue:
        return

    # Get the next output packet
    actual = self.actual_queue.popleft()

    # Get the ID from the packet
    actual_id = actual.id if hasattr(actual, 'id') else None

    # Determine which queue to compare against based on ID
    if actual_id in [0xAA, 0xA]:
        expected_queue = self.combined_queue_a
        channel = 'A'
    elif actual_id in [0xBB, 0xB]:
        expected_queue = self.combined_queue_b
        channel = 'B'
    elif actual_id in [0xCC, 0xC]:
        expected_queue = self.combined_queue_c
        channel = 'C'
    elif actual_id in [0xDD, 0xD]:
        expected_queue = self.combined_queue_d
        channel = 'D'
    else:
        self.log.error(f"Output packet has unknown ID: 0x{actual_id:X}")
        self.error_count += 1
        return

    # Check if we have an expected packet
    if not expected_queue:
        self.log.error(f"No expected packets for channel {channel} (ID=0x{actual_id:X})")
        self.error_count += 1
        return

    # Get expected packet and compare
    expected = expected_queue.popleft()
    self.comparison_count += 1

    # Get data values from both packets
    expected_data0 = expected.data0 if hasattr(expected, 'data0') else 0
    expected_data1 = expected.data1 if hasattr(expected, 'data1') else 0
    expected_data2 = expected.data2 if hasattr(expected, 'data2') else 0
    expected_data3 = expected.data3 if hasattr(expected, 'data3') else 0
    
    actual_data0 = actual.data0 if hasattr(actual, 'data0') else 0
    actual_data1 = actual.data1 if hasattr(actual, 'data1') else 0
    actual_data2 = actual.data2 if hasattr(actual, 'data2') else 0
    actual_data3 = actual.data3 if hasattr(actual, 'data3') else 0

    # Compare packets
    if (actual_data0 != expected_data0 or
        actual_data1 != expected_data1 or
        actual_data2 != expected_data2 or
        actual_data3 != expected_data3):

        self.log.error(f"Packet mismatch for channel {channel} (ID=0x{actual_id:X}):")
        self.log.error(f"  Expected: data0=0x{expected_data0:X}, data1=0x{expected_data1:X}, "
                        f"data2=0x{expected_data2:X}, data3=0x{expected_data3:X}")
        self.log.error(f"  Actual: data0=0x{actual_data0:X}, data1=0x{actual_data1:X}, "
                        f"data2=0x{actual_data2:X}, data3=0x{actual_data3:X}")
        self.error_count += 1
    else:
        self.log.debug(f"Packet match for channel {channel} (ID=0x{actual_id:X})")
```

### check_remaining_data / report

Checks for leftover data and generates a report.

```python
def check_remaining_data(self):
    """
    Check if any queues have leftover data

    Returns:
        Number of errors (non-zero if any queue has leftover data)
    """
    errors = 0

    # Check input queues
    if self.queue_a:
        self.log.error(f"Channel A has {len(self.queue_a)} leftover input packets")
        errors += 1

    # Similar checks for other queues
    # ...

    return errors

def report(self):
    """
    Generate a report and return the number of errors

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

    if total_errors == 0:
        self.log.info("  TEST PASSED: All packets verified successfully")
    else:
        self.log.error(f"  TEST FAILED: {total_errors} errors detected")

    return total_errors
```

## Example Usage

Basic usage of the GAXI data collection testbench:

```python
from CocoTBFramework.tbclasses.gaxi.gaxi_data_collect_tb import DataCollectTB

@cocotb.test()
async def test_data_collect(dut):
    # Set environment variables
    os.environ['DATA_WIDTH'] = '32'
    os.environ['ID_WIDTH'] = '4'
    os.environ['OUTPUT_FIFO_DEPTH'] = '16'
    os.environ['SEED'] = '12345'
    
    # Create testbench
    tb = DataCollectTB(dut)
    
    # Run simple test
    passed = await tb.run_simple_test(packets_per_channel=40)
    assert passed, "Simple test failed"
    
    # Run weighted arbitration test
    passed = await tb.run_weighted_arbiter_test()
    assert passed, "Weighted arbitration test failed"
    
    # Run stress test
    passed = await tb.run_stress_test(duration_clocks=10000)
    assert passed, "Stress test failed"
```

Testing with custom weight configurations:

```python
# Define custom weights
weights_list = [
    (8, 8, 8, 8),   # Equal weights
    (15, 5, 2, 1),  # Heavily weighted towards A
    (1, 2, 5, 15),  # Heavily weighted towards D
    (0, 15, 15, 0), # B and C only
]

# Run weighted test with custom weights
result = await tb.run_weighted_arbiter_test(weights_list)
assert result, "Custom weighted test failed"
```

## Implementation Notes

- The testbench uses multi-channel configuration for testing data collection
- Channel identification is based on ID values (0xAA, 0xBB, 0xCC, 0xDD)
- The scoreboard groups 4 input packets into one output packet
- Randomization controls timing behavior
- Weighted arbitration testing verifies channel priority behavior
- Concurrent tasks handle multi-channel traffic
- Signal mapping connects to specific DUT signals

## Environment Variables

The testbench configuration is controlled by these variables:

- **DATA_WIDTH**: Width of data fields in bits
- **ID_WIDTH**: Width of ID field in bits
- **OUTPUT_FIFO_DEPTH**: Depth of output FIFO buffer
- **SEED**: Random seed for reproducible testing

## See Also

- [GAXI Buffer Multi](gaxi_buffer_multi.md) - Multi-signal GAXI buffer testbench
- [GAXI Packet](../../components/gaxi/gaxi_packet.md) - GAXI packet structure
- [WeightedRoundRobinArbiterMonitor](../../components/arbiter_monitor.md) - Arbiter monitoring

## Navigation

[↑ GAXI Testbenches Index](index.md) | [↑ TBClasses Index](../index.md) | [↑ CocoTBFramework Index](../../index.md)
