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

**[← Back to Test Tutorial Index](index.md)**

# Building Custom Test Classes

A comprehensive guide to creating reusable verification IP, extending framework base classes, implementing custom packet types, writing monitors and scoreboards, and applying factory patterns for scalable testbench development.

## Table of Contents

- [Overview](#overview)
- [Extending TBBase](#extending-tbbase)
- [Custom Component Classes](#custom-component-classes)
- [Custom Packet Types](#custom-packet-types)
- [Field Configuration Patterns](#field-configuration-patterns)
- [Custom Monitors](#custom-monitors)
- [Custom Scoreboards](#custom-scoreboards)
- [Factory Patterns](#factory-patterns)
- [Reusable Verification IP](#reusable-verification-ip)
- [Best Practices](#best-practices)
- [Anti-Patterns to Avoid](#anti-patterns-to-avoid)

## Overview

The RTL Design Sherpa framework provides extensible base classes for building custom verification components. This guide demonstrates how to create reusable, maintainable testbench infrastructure.

### Framework Architecture

```
Custom Verification IP Architecture:

┌─────────────────────────────────────────────────────┐
│ Custom Testbench Classes                            │
│   - Inherit from TBBase                             │
│   - Project-specific test infrastructure            │
│   - Located in projects/{name}/dv/tbclasses/       │
└─────────────────────────────────────────────────────┘
                         ↓
┌─────────────────────────────────────────────────────┐
│ Custom Components (BFMs, Drivers, Monitors)         │
│   - Protocol-specific implementations               │
│   - Extend GAXI base classes                        │
│   - Located in bin/CocoTBFramework/components/      │
└─────────────────────────────────────────────────────┘
                         ↓
┌─────────────────────────────────────────────────────┐
│ Framework Base Classes                              │
│   - TBBase (testbench utilities)                    │
│   - GAXI components (protocol infrastructure)       │
│   - Located in bin/CocoTBFramework/tbclasses/shared/│
└─────────────────────────────────────────────────────┘
```

### When to Create Custom Classes

| Create Custom Class When | Keep Inline When |
|--------------------------|------------------|
| >100 lines of code | <50 lines |
| Used across 3+ tests | Single test only |
| Protocol complexity | Simple stimulus/response |
| Reusable across projects | Project-specific logic |
| Standalone testable | Tightly coupled to one test |

## Extending TBBase

All custom testbench classes should inherit from `TBBase`, which provides clock management, reset control, logging, and utility functions.

### Basic TBBase Extension

```python
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
import cocotb
from cocotb.triggers import RisingEdge

class MyModuleTB(TBBase):
    """
    Custom testbench for MyModule.

    Architecture:
        - AXI4 master interface for memory access
        - APB slave for configuration
        - Custom control signals

    Inherits from TBBase:
        - Clock management (start_clock, wait_clocks)
        - Reset control (assert_reset, deassert_reset)
        - Logging (self.log)
        - Utilities (convert_to_int, mark_progress)
    """

    def __init__(self, dut):
        """
        Initialize testbench.

        Args:
            dut: Device under test (cocotb handle)
        """
        # MANDATORY: Call parent constructor
        super().__init__(dut)

        # Define clock name (used by wait_clocks)
        self.clk_name = 'aclk'

        # Initialize protocol interfaces
        from CocoTBFramework.components.axi4.axi4_interfaces import AXI4MasterWrite

        self.axi_master = AXI4MasterWrite(
            dut=dut,
            clock=dut.aclk,
            prefix="m_axi_",
            data_width=32,
            addr_width=32,
            id_width=4,
            log=self.log
        )

        # Custom state tracking
        self.operation_count = 0
        self.error_count = 0

    # MANDATORY: Implement three required methods
    async def setup_clocks_and_reset(self):
        """
        Setup clocks and perform reset sequence.

        This is the standard entry point for test initialization.
        """
        # Start clock (inherited from TBBase)
        await self.start_clock(self.clk_name, freq=10, units='ns')

        # Assert reset
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)

        # Deassert reset
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

        self.log.info("Initialization complete")

    async def assert_reset(self):
        """Assert active-low reset."""
        self.dut.aresetn.value = 0
        # Add any module-specific reset initialization
        self.dut.enable.value = 0
        self.dut.start.value = 0

    async def deassert_reset(self):
        """Deassert active-low reset."""
        self.dut.aresetn.value = 1

    # Custom high-level operations
    async def configure_module(self, config_dict):
        """
        Configure module via control registers.

        Args:
            config_dict: Dictionary of {register_name: value}
        """
        self.log.info(f"Configuring module: {len(config_dict)} registers")

        for reg_name, value in config_dict.items():
            # Use DUT signals directly
            signal = getattr(self.dut, reg_name)
            signal.value = value
            self.log.debug(f"  {reg_name} = 0x{value:08X}")

        await self.wait_clocks(self.clk_name, 2)

    async def start_operation(self):
        """Start module operation."""
        self.dut.start.value = 1
        await self.wait_clocks(self.clk_name, 1)
        self.dut.start.value = 0
        self.operation_count += 1

    async def wait_for_completion(self, timeout_cycles=1000):
        """
        Wait for operation to complete.

        Args:
            timeout_cycles: Maximum cycles to wait

        Returns:
            True if completed, False if timeout

        Raises:
            TimeoutError: If operation doesn't complete
        """
        cycles = 0

        while int(self.dut.done.value) == 0:
            if cycles >= timeout_cycles:
                raise TimeoutError(f"Operation timeout after {timeout_cycles} cycles")

            await self.wait_clocks(self.clk_name, 1)
            cycles += 1

        self.log.info(f"Operation completed in {cycles} cycles")
        return True

    async def read_result(self):
        """Read operation result."""
        result = int(self.dut.result.value)
        status = int(self.dut.status.value)

        if status != 0:
            self.error_count += 1
            self.log.warning(f"Operation error: status=0x{status:02X}")

        return result, status

    # Utility method using TBBase functionality
    async def run_test_operation(self, config, expected_result=None):
        """
        Execute complete test operation with verification.

        Args:
            config: Configuration dictionary
            expected_result: Expected result (optional)

        Returns:
            Test passed status
        """
        # Configure
        await self.configure_module(config)

        # Start
        await self.start_operation()

        # Wait for completion
        await self.wait_for_completion()

        # Read result
        result, status = await self.read_result()

        # Verify if expected result provided
        if expected_result is not None:
            if result == expected_result and status == 0:
                self.log.info(f"Test PASSED: result=0x{result:08X}")
                return True
            else:
                self.log.error(f"Test FAILED: expected=0x{expected_result:08X}, got=0x{result:08X}, status={status}")
                return False

        return status == 0


# Usage in test
@cocotb.test()
async def test_my_module_basic(dut):
    """Test basic module operation."""
    tb = MyModuleTB(dut)
    await tb.setup_clocks_and_reset()

    config = {
        'mode': 0x1,
        'threshold': 0x100,
        'enable': 0x1
    }

    success = await tb.run_test_operation(config, expected_result=0x42)
    assert success, "Test operation failed"
```

### Advanced TBBase Extension with Background Tasks

```python
class AdvancedTB(TBBase):
    """
    Advanced testbench with background monitoring.

    Demonstrates:
        - Background coroutines
        - Continuous monitoring
        - Event collection
        - Statistics tracking
    """

    def __init__(self, dut):
        super().__init__(dut)
        self.clk_name = 'aclk'

        # Monitoring state
        self.monitor_active = False
        self.events = []
        self.statistics = {
            'operations': 0,
            'errors': 0,
            'warnings': 0
        }

    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def start_monitoring(self):
        """Start background monitoring tasks."""
        self.monitor_active = True

        # Launch multiple monitoring coroutines
        cocotb.start_soon(self.monitor_outputs())
        cocotb.start_soon(self.monitor_errors())
        cocotb.start_soon(self.monitor_performance())

        self.log.info("Background monitoring started")

    async def stop_monitoring(self):
        """Stop background monitoring."""
        self.monitor_active = False
        await self.wait_clocks(self.clk_name, 5)  # Drain pipeline
        self.log.info("Background monitoring stopped")

    async def monitor_outputs(self):
        """Monitor output interface continuously."""
        while self.monitor_active:
            await self.wait_clocks(self.clk_name, 1)

            if int(self.dut.output_valid.value) == 1:
                output_data = int(self.dut.output_data.value)
                timestamp = cocotb.utils.get_sim_time(units='ns')

                self.events.append({
                    'type': 'output',
                    'data': output_data,
                    'time': timestamp
                })

                self.statistics['operations'] += 1
                self.log.debug(f"Output: 0x{output_data:08X} @ {timestamp}ns")

    async def monitor_errors(self):
        """Monitor error conditions."""
        while self.monitor_active:
            await self.wait_clocks(self.clk_name, 1)

            if int(self.dut.error.value) == 1:
                error_code = int(self.dut.error_code.value)
                timestamp = cocotb.utils.get_sim_time(units='ns')

                self.events.append({
                    'type': 'error',
                    'code': error_code,
                    'time': timestamp
                })

                self.statistics['errors'] += 1
                self.log.warning(f"Error detected: code={error_code} @ {timestamp}ns")

    async def monitor_performance(self):
        """Monitor performance counters."""
        while self.monitor_active:
            await self.wait_clocks(self.clk_name, 100)  # Sample every 100 cycles

            if hasattr(self.dut, 'perf_counter'):
                counter = int(self.dut.perf_counter.value)
                self.log.debug(f"Performance counter: {counter}")

    def get_statistics_report(self):
        """Generate statistics report."""
        report = []
        report.append("\n" + "="*60)
        report.append("Testbench Statistics")
        report.append("="*60)
        report.append(f"Operations: {self.statistics['operations']}")
        report.append(f"Errors:     {self.statistics['errors']}")
        report.append(f"Warnings:   {self.statistics['warnings']}")
        report.append(f"Events:     {len(self.events)}")
        report.append("="*60)
        return '\n'.join(report)


@cocotb.test()
async def test_with_monitoring(dut):
    """Test with continuous background monitoring."""
    tb = AdvancedTB(dut)
    await tb.setup_clocks_and_reset()

    # Start monitoring
    await tb.start_monitoring()

    # Run test operations
    for i in range(100):
        # Test operations here
        await tb.wait_clocks('aclk', 10)

    # Stop monitoring
    await tb.stop_monitoring()

    # Generate report
    report = tb.get_statistics_report()
    tb.log.info(report)

    # Verify no errors
    assert tb.statistics['errors'] == 0, "Errors detected during test"
```

## Custom Component Classes

Create custom component classes for protocol-specific BFMs, drivers, and monitors.

### Custom Driver Component

```python
from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster
from CocoTBFramework.components.gaxi.gaxi_field_config import GAXIFieldConfig

class CustomProtocolMaster:
    """
    Custom protocol master driver.

    Protocol: Simple request-response with flow control
        - req_valid, req_ready handshake
        - Request fields: addr, data, cmd
        - Response: resp_valid, resp_data
    """

    def __init__(self, dut, clock, prefix="", log=None):
        """
        Initialize custom protocol master.

        Args:
            dut: Device under test
            clock: Clock signal
            prefix: Signal name prefix
            log: Logger instance
        """
        self.dut = dut
        self.clock = clock
        self.log = log
        self.prefix = prefix

        # Create field configuration
        field_config = GAXIFieldConfig()
        field_config.add_field('addr', 32, True)   # 32-bit address, required
        field_config.add_field('data', 32, True)   # 32-bit data, required
        field_config.add_field('cmd', 4, True)     # 4-bit command, required

        # Use GAXI master for handshaking
        self.request_channel = GAXIMaster(
            dut=dut,
            title="CustomProtocolRequest",
            prefix=prefix,
            clock=clock,
            field_config=field_config,
            pkt_prefix="req",
            multi_sig=True,
            protocol_type='custom_request',
            log=log
        )

        # Track outstanding requests
        self.outstanding_requests = []

    async def send_request(self, addr, data, cmd):
        """
        Send protocol request.

        Args:
            addr: Target address
            data: Request data
            cmd: Command code

        Returns:
            Request ID for tracking
        """
        # Create request packet
        request = {
            'addr': addr,
            'data': data,
            'cmd': cmd
        }

        # Send via GAXI channel
        await self.request_channel.send(request)

        # Track request
        request_id = len(self.outstanding_requests)
        self.outstanding_requests.append({
            'id': request_id,
            'addr': addr,
            'data': data,
            'cmd': cmd,
            'completed': False
        })

        if self.log:
            self.log.debug(f"Sent request {request_id}: addr=0x{addr:08X}, cmd={cmd}")

        return request_id

    async def wait_response(self):
        """
        Wait for protocol response.

        Returns:
            Response data
        """
        # Poll response signals
        while True:
            await RisingEdge(self.clock)

            resp_valid_sig = getattr(self.dut, f"{self.prefix}resp_valid")
            if int(resp_valid_sig.value) == 1:
                resp_data_sig = getattr(self.dut, f"{self.prefix}resp_data")
                resp_data = int(resp_data_sig.value)

                if self.log:
                    self.log.debug(f"Received response: data=0x{resp_data:08X}")

                return resp_data

    async def read_transaction(self, addr):
        """
        Perform read transaction.

        Args:
            addr: Read address

        Returns:
            Read data
        """
        # Send read request (cmd=0 for read)
        await self.send_request(addr, 0, cmd=0)

        # Wait for response
        data = await self.wait_response()

        if self.log:
            self.log.info(f"Read: addr=0x{addr:08X} => data=0x{data:08X}")

        return data

    async def write_transaction(self, addr, data):
        """
        Perform write transaction.

        Args:
            addr: Write address
            data: Write data
        """
        # Send write request (cmd=1 for write)
        await self.send_request(addr, data, cmd=1)

        # Wait for response (write acknowledgment)
        resp = await self.wait_response()

        if self.log:
            self.log.info(f"Write: addr=0x{addr:08X} <= data=0x{data:08X}, resp={resp}")


# Usage
@cocotb.test()
async def test_custom_protocol(dut):
    """Test custom protocol driver."""
    from CocoTBFramework.tbclasses.shared.tbbase import TBBase

    tb = TBBase(dut)
    await tb.start_clock('clk', freq=10, units='ns')

    # Initialize custom driver
    driver = CustomProtocolMaster(
        dut=dut,
        clock=dut.clk,
        prefix="custom_",
        log=tb.log
    )

    # Perform transactions
    await driver.write_transaction(0x1000, 0xDEADBEEF)
    read_data = await driver.read_transaction(0x1000)

    assert read_data == 0xDEADBEEF, f"Data mismatch: {read_data:08X}"
```

## Custom Packet Types

Define structured packet types for complex data handling.

### Custom Packet Class

```python
from dataclasses import dataclass, field
from typing import List, Optional

@dataclass
class CustomPacket:
    """
    Custom packet type for specialized protocol.

    Fields:
        - header: Packet header with metadata
        - payload: Variable-length data payload
        - checksum: Data integrity check
    """

    # Header fields
    packet_id: int
    packet_type: int
    source_id: int
    dest_id: int

    # Payload
    payload: List[int] = field(default_factory=list)

    # Metadata
    timestamp: Optional[int] = None
    checksum: Optional[int] = None

    def compute_checksum(self):
        """Compute simple checksum over payload."""
        if not self.payload:
            return 0
        return sum(self.payload) & 0xFFFF

    def validate(self):
        """Validate packet integrity."""
        if self.checksum is None:
            self.checksum = self.compute_checksum()

        computed = self.compute_checksum()
        return computed == self.checksum

    def serialize(self):
        """
        Serialize packet to list of integers.

        Format:
            [header_word0, header_word1, payload_len, payload..., checksum]
        """
        header_word0 = (self.packet_id << 16) | (self.packet_type << 8)
        header_word1 = (self.source_id << 16) | self.dest_id

        serialized = [
            header_word0,
            header_word1,
            len(self.payload)
        ]

        serialized.extend(self.payload)

        if self.checksum is None:
            self.checksum = self.compute_checksum()
        serialized.append(self.checksum)

        return serialized

    @classmethod
    def deserialize(cls, data):
        """
        Deserialize packet from list of integers.

        Args:
            data: List of integer words

        Returns:
            CustomPacket instance
        """
        header_word0 = data[0]
        header_word1 = data[1]
        payload_len = data[2]

        packet_id = (header_word0 >> 16) & 0xFFFF
        packet_type = (header_word0 >> 8) & 0xFF
        source_id = (header_word1 >> 16) & 0xFFFF
        dest_id = header_word1 & 0xFFFF

        payload = data[3:3+payload_len]
        checksum = data[3+payload_len]

        return cls(
            packet_id=packet_id,
            packet_type=packet_type,
            source_id=source_id,
            dest_id=dest_id,
            payload=payload,
            checksum=checksum
        )

    def __repr__(self):
        """String representation."""
        return (f"CustomPacket(id={self.packet_id}, type={self.packet_type}, "
                f"src={self.source_id}, dst={self.dest_id}, "
                f"payload_len={len(self.payload)}, checksum=0x{self.checksum:04X})")


# Usage with driver
class CustomPacketDriver:
    """Driver for custom packet protocol."""

    def __init__(self, master_channel, log):
        self.master = master_channel
        self.log = log

    async def send_packet(self, packet: CustomPacket):
        """Send custom packet."""
        # Serialize packet
        serialized = packet.serialize()

        self.log.info(f"Sending packet: {packet}")

        # Send each word
        for i, word in enumerate(serialized):
            gaxi_packet = {
                'tdata': word,
                'tkeep': 0xF,
                'tlast': 1 if i == len(serialized)-1 else 0,
                'tuser': 0
            }
            await self.master.send(gaxi_packet)

    async def receive_packet(self, slave_channel) -> CustomPacket:
        """Receive custom packet."""
        received_words = []

        while True:
            gaxi_packet = await slave_channel.recv()
            received_words.append(gaxi_packet['tdata'])

            if gaxi_packet['tlast']:
                break

        # Deserialize packet
        packet = CustomPacket.deserialize(received_words)

        # Validate
        if not packet.validate():
            self.log.warning(f"Packet checksum mismatch: {packet}")

        self.log.info(f"Received packet: {packet}")
        return packet


@cocotb.test()
async def test_custom_packets(dut):
    """Test custom packet transmission."""
    from CocoTBFramework.tbclasses.shared.tbbase import TBBase
    from CocoTBFramework.components.axis4.axis4_master import AXIS4Master
    from CocoTBFramework.components.axis4.axis4_slave import AXIS4Slave

    tb = TBBase(dut)
    await tb.start_clock('aclk', freq=10, units='ns')

    # Initialize interfaces
    axis_master = AXIS4Master(dut, dut.aclk, "s_axis_", 32, tb.log)
    axis_slave = AXIS4Slave(dut, dut.aclk, "m_axis_", 32, tb.log)

    # Initialize driver
    driver = CustomPacketDriver(axis_master, tb.log)

    # Create and send packet
    packet = CustomPacket(
        packet_id=1,
        packet_type=0x10,
        source_id=0xA,
        dest_id=0xB,
        payload=[0x100, 0x200, 0x300, 0x400]
    )

    await driver.send_packet(packet)

    # Receive and verify
    received = await driver.receive_packet(axis_slave)

    assert received.packet_id == packet.packet_id
    assert received.payload == packet.payload
    assert received.validate(), "Packet validation failed"
```

## Field Configuration Patterns

Use field configurations for flexible signal mapping.

### Dynamic Field Configuration

```python
from CocoTBFramework.components.gaxi.gaxi_field_config import GAXIFieldConfig

class FlexibleProtocolConfig:
    """
    Flexible protocol configuration builder.

    Supports multiple protocol variants with different field sets.
    """

    @staticmethod
    def create_config(variant='standard', **kwargs):
        """
        Create field configuration for protocol variant.

        Args:
            variant: Protocol variant name
            **kwargs: Variant-specific parameters

        Returns:
            GAXIFieldConfig instance
        """
        config = GAXIFieldConfig()

        if variant == 'standard':
            # Standard variant: basic fields
            config.add_field('addr', 32, required=True)
            config.add_field('data', kwargs.get('data_width', 32), required=True)
            config.add_field('cmd', 4, required=True)

        elif variant == 'extended':
            # Extended variant: additional metadata
            config.add_field('addr', 32, required=True)
            config.add_field('data', kwargs.get('data_width', 64), required=True)
            config.add_field('cmd', 4, required=True)
            config.add_field('user_id', 8, required=False)  # Optional
            config.add_field('timestamp', 32, required=False)  # Optional

        elif variant == 'burst':
            # Burst variant: burst transaction support
            config.add_field('addr', 32, required=True)
            config.add_field('data', kwargs.get('data_width', 32), required=True)
            config.add_field('cmd', 4, required=True)
            config.add_field('burst_len', 8, required=True)
            config.add_field('burst_size', 3, required=True)

        elif variant == 'custom':
            # Custom variant: user-defined fields
            fields = kwargs.get('fields', [])
            for field_name, field_width, required in fields:
                config.add_field(field_name, field_width, required)

        else:
            raise ValueError(f"Unknown variant: {variant}")

        return config


# Usage
@cocotb.test()
async def test_flexible_protocol(dut):
    """Test flexible protocol configuration."""
    from CocoTBFramework.components.gaxi.gaxi_master import GAXIMaster

    # Create extended variant
    config = FlexibleProtocolConfig.create_config(
        variant='extended',
        data_width=64
    )

    master = GAXIMaster(
        dut=dut,
        title="ExtendedProtocol",
        prefix="ext_",
        clock=dut.clk,
        field_config=config,
        pkt_prefix="req",
        multi_sig=True,
        log=None
    )

    # Send packet with extended fields
    packet = {
        'addr': 0x1000,
        'data': 0xDEADBEEFCAFEBABE,
        'cmd': 0x5,
        'user_id': 0x42,           # Extended field
        'timestamp': 0x12345678     # Extended field
    }

    await master.send(packet)
```

## Custom Monitors

Build custom monitors for specialized observability.

### Transaction Monitor

```python
from collections import deque
import cocotb
from cocotb.triggers import RisingEdge

class TransactionMonitor:
    """
    Generic transaction monitor.

    Monitors valid/ready handshake and captures transaction details.
    """

    def __init__(self, dut, clock, prefix, field_list, log):
        """
        Initialize transaction monitor.

        Args:
            dut: Device under test
            clock: Clock signal
            prefix: Signal prefix
            field_list: List of (field_name, width) tuples
            log: Logger
        """
        self.dut = dut
        self.clock = clock
        self.prefix = prefix
        self.field_list = field_list
        self.log = log

        # Transaction queue
        self.transactions = deque()

        # Statistics
        self.stats = {
            'total_transactions': 0,
            'total_cycles': 0,
            'wait_cycles': 0
        }

        # Monitoring control
        self.active = False

    async def start_monitoring(self):
        """Start background monitoring."""
        self.active = True
        cocotb.start_soon(self.monitor_loop())
        self.log.info(f"Monitor started: {self.prefix}")

    async def stop_monitoring(self):
        """Stop monitoring."""
        self.active = False
        self.log.info(f"Monitor stopped: {self.prefix}")

    async def monitor_loop(self):
        """Main monitoring loop."""
        while self.active:
            await RisingEdge(self.clock)

            # Get handshake signals
            valid_sig = getattr(self.dut, f"{self.prefix}valid")
            ready_sig = getattr(self.dut, f"{self.prefix}ready")

            self.stats['total_cycles'] += 1

            # Check for transaction
            if int(valid_sig.value) == 1:
                if int(ready_sig.value) == 1:
                    # Transaction occurred
                    transaction = self.capture_transaction()
                    self.transactions.append(transaction)
                    self.stats['total_transactions'] += 1

                    self.log.debug(f"Transaction {self.stats['total_transactions']}: {transaction}")
                else:
                    # Valid but not ready (wait state)
                    self.stats['wait_cycles'] += 1

    def capture_transaction(self):
        """Capture current transaction fields."""
        transaction = {}

        for field_name, field_width in self.field_list:
            signal_name = f"{self.prefix}{field_name}"
            signal = getattr(self.dut, signal_name)
            transaction[field_name] = int(signal.value)

        # Add timestamp
        transaction['timestamp'] = cocotb.utils.get_sim_time(units='ns')

        return transaction

    def get_transaction(self):
        """Get next transaction from queue."""
        if self.transactions:
            return self.transactions.popleft()
        return None

    def get_statistics(self):
        """Get monitoring statistics."""
        efficiency = 0
        if self.stats['total_cycles'] > 0:
            efficiency = (self.stats['total_transactions'] / self.stats['total_cycles']) * 100

        return {
            'transactions': self.stats['total_transactions'],
            'total_cycles': self.stats['total_cycles'],
            'wait_cycles': self.stats['wait_cycles'],
            'efficiency': efficiency
        }


# Usage
@cocotb.test()
async def test_with_monitor(dut):
    """Test with transaction monitoring."""
    from CocoTBFramework.tbclasses.shared.tbbase import TBBase

    tb = TBBase(dut)
    await tb.start_clock('clk', freq=10, units='ns')

    # Create monitor
    monitor = TransactionMonitor(
        dut=dut,
        clock=dut.clk,
        prefix="m_axis_",
        field_list=[('data', 32), ('keep', 4), ('last', 1)],
        log=tb.log
    )

    # Start monitoring
    await monitor.start_monitoring()

    # Run test (transactions monitored in background)
    # ... test operations ...

    await tb.wait_clocks('clk', 1000)

    # Stop monitoring
    await monitor.stop_monitoring()

    # Check results
    stats = monitor.get_statistics()
    tb.log.info(f"Monitor statistics: {stats}")

    # Verify transactions
    captured_count = stats['transactions']
    assert captured_count > 0, "No transactions captured"
```

## Custom Scoreboards

Implement scoreboards for transaction verification.

### Queue-Based Scoreboard

```python
from collections import deque

class QueueScoreboard:
    """
    Simple queue-based scoreboard.

    Compares expected vs actual transactions using queues.
    """

    def __init__(self, name, log):
        """
        Initialize scoreboard.

        Args:
            name: Scoreboard name
            log: Logger
        """
        self.name = name
        self.log = log

        # Transaction queues
        self.expected_queue = deque()
        self.actual_queue = deque()

        # Statistics
        self.stats = {
            'matches': 0,
            'mismatches': 0,
            'missing': 0,
            'unexpected': 0
        }

    def expect_transaction(self, transaction):
        """Add expected transaction."""
        self.expected_queue.append(transaction)
        self.log.debug(f"{self.name}: Expected {transaction}")

    def observe_transaction(self, transaction):
        """Observe actual transaction and verify."""
        self.actual_queue.append(transaction)

        if not self.expected_queue:
            # Unexpected transaction
            self.stats['unexpected'] += 1
            self.log.error(f"{self.name}: Unexpected transaction: {transaction}")
            return False

        expected = self.expected_queue.popleft()

        if self.compare_transactions(expected, transaction):
            self.stats['matches'] += 1
            self.log.debug(f"{self.name}: Match {transaction}")
            return True
        else:
            self.stats['mismatches'] += 1
            self.log.error(f"{self.name}: Mismatch")
            self.log.error(f"  Expected: {expected}")
            self.log.error(f"  Got:      {transaction}")
            return False

    def compare_transactions(self, expected, actual):
        """Compare two transactions for equality."""
        # Basic comparison (can be customized)
        if isinstance(expected, dict) and isinstance(actual, dict):
            # Compare dictionary fields
            for key in expected:
                if key not in actual:
                    return False
                if expected[key] != actual[key]:
                    return False
            return True
        else:
            # Direct comparison
            return expected == actual

    def check_complete(self):
        """Verify all expected transactions observed."""
        if self.expected_queue:
            self.stats['missing'] = len(self.expected_queue)
            self.log.error(f"{self.name}: {self.stats['missing']} transactions missing")
            return False
        return True

    def generate_report(self):
        """Generate verification report."""
        total_checks = self.stats['matches'] + self.stats['mismatches']
        success_rate = 0
        if total_checks > 0:
            success_rate = (self.stats['matches'] / total_checks) * 100

        report = []
        report.append(f"\n{'='*60}")
        report.append(f"Scoreboard Report: {self.name}")
        report.append(f"{'='*60}")
        report.append(f"Matches:     {self.stats['matches']}")
        report.append(f"Mismatches:  {self.stats['mismatches']}")
        report.append(f"Missing:     {self.stats['missing']}")
        report.append(f"Unexpected:  {self.stats['unexpected']}")
        report.append(f"Success Rate: {success_rate:.1f}%")
        report.append(f"{'='*60}")

        return '\n'.join(report)


# Usage
@cocotb.test()
async def test_with_scoreboard(dut):
    """Test with scoreboard verification."""
    from CocoTBFramework.tbclasses.shared.tbbase import TBBase

    tb = TBBase(dut)
    await tb.start_clock('clk', freq=10, units='ns')

    # Create scoreboard
    scoreboard = QueueScoreboard("DataPath", tb.log)

    # Setup expected transactions
    test_data = [0x100, 0x200, 0x300, 0x400]
    for data in test_data:
        scoreboard.expect_transaction({'data': data})

    # Run test and observe outputs
    for data in test_data:
        # Send input
        # ... (send data to DUT)

        # Observe output (simulated here)
        output = data  # In reality, read from DUT
        scoreboard.observe_transaction({'data': output})

    # Verify completion
    assert scoreboard.check_complete(), "Not all transactions observed"

    # Generate report
    report = scoreboard.generate_report()
    tb.log.info(report)

    # Check success
    assert scoreboard.stats['mismatches'] == 0, "Transaction mismatches detected"
```

## Factory Patterns

Use factory patterns for scalable test component creation.

### Component Factory

```python
class ComponentFactory:
    """
    Factory for creating test components.

    Centralizes component creation and configuration.
    """

    @staticmethod
    def create_axi_master(dut, clock, prefix, config=None):
        """
        Create AXI4 master with standard configuration.

        Args:
            dut: Device under test
            clock: Clock signal
            prefix: Signal prefix
            config: Optional configuration dictionary

        Returns:
            AXI4MasterWrite instance
        """
        from CocoTBFramework.components.axi4.axi4_interfaces import AXI4MasterWrite

        # Default configuration
        default_config = {
            'data_width': 32,
            'addr_width': 32,
            'id_width': 4,
            'user_width': 1
        }

        # Merge with provided config
        if config:
            default_config.update(config)

        return AXI4MasterWrite(
            dut=dut,
            clock=clock,
            prefix=prefix,
            **default_config
        )

    @staticmethod
    def create_apb_master(dut, clock, prefix, config=None):
        """Create APB master."""
        from CocoTBFramework.components.apb.apb_components import APBMaster

        default_config = {
            'addr_width': 16,
            'data_width': 32
        }

        if config:
            default_config.update(config)

        return APBMaster(
            dut=dut,
            clock=clock,
            prefix=prefix,
            **default_config
        )

    @staticmethod
    def create_axis_master(dut, clock, prefix, config=None):
        """Create AXIS master."""
        from CocoTBFramework.components.axis4.axis4_master import AXIS4Master

        default_config = {
            'data_width': 32
        }

        if config:
            default_config.update(config)

        return AXIS4Master(
            dut=dut,
            clock=clock,
            prefix=prefix,
            **default_config
        )

    @classmethod
    def create_system_components(cls, dut, clock, interfaces):
        """
        Create multiple components for system testbench.

        Args:
            dut: Device under test
            clock: Clock signal
            interfaces: Dictionary of {name: (type, prefix, config)}

        Returns:
            Dictionary of {name: component}
        """
        components = {}

        for name, (ifc_type, prefix, config) in interfaces.items():
            if ifc_type == 'axi_master':
                component = cls.create_axi_master(dut, clock, prefix, config)
            elif ifc_type == 'apb_master':
                component = cls.create_apb_master(dut, clock, prefix, config)
            elif ifc_type == 'axis_master':
                component = cls.create_axis_master(dut, clock, prefix, config)
            else:
                raise ValueError(f"Unknown interface type: {ifc_type}")

            components[name] = component

        return components


# Usage
@cocotb.test()
async def test_with_factory(dut):
    """Test using component factory."""
    from CocoTBFramework.tbclasses.shared.tbbase import TBBase

    tb = TBBase(dut)
    await tb.start_clock('aclk', freq=10, units='ns')

    # Define system interfaces
    interfaces = {
        'mem': ('axi_master', 'm_axi_', {'data_width': 64}),
        'cfg': ('apb_master', 'apb_', {'addr_width': 16}),
        'stream': ('axis_master', 's_axis_', {'data_width': 32})
    }

    # Create all components
    components = ComponentFactory.create_system_components(
        dut, dut.aclk, interfaces
    )

    # Use components
    mem_if = components['mem']
    cfg_if = components['cfg']
    stream_if = components['stream']

    # ... test operations ...
```

## Reusable Verification IP

### Verification IP Package Structure

```python
"""
Reusable Verification IP Package

Structure:
    my_vip/
    ├── __init__.py
    ├── drivers/
    │   ├── protocol_driver.py
    │   └── advanced_driver.py
    ├── monitors/
    │   ├── protocol_monitor.py
    │   └── performance_monitor.py
    ├── scoreboards/
    │   └── protocol_scoreboard.py
    ├── sequences/
    │   └── test_sequences.py
    └── utils/
        └── helpers.py
"""

# __init__.py
from .drivers.protocol_driver import ProtocolDriver
from .monitors.protocol_monitor import ProtocolMonitor
from .scoreboards.protocol_scoreboard import ProtocolScoreboard
from .sequences.test_sequences import BasicSequence, StressSequence

__all__ = [
    'ProtocolDriver',
    'ProtocolMonitor',
    'ProtocolScoreboard',
    'BasicSequence',
    'StressSequence'
]

__version__ = '1.0.0'
```

### VIP Usage Example

```python
# Using VIP in test
from my_vip import ProtocolDriver, ProtocolMonitor, ProtocolScoreboard, BasicSequence

@cocotb.test()
async def test_with_vip(dut):
    """Test using reusable VIP."""
    tb = TBBase(dut)
    await tb.setup_clocks_and_reset()

    # Instantiate VIP components
    driver = ProtocolDriver(dut, dut.clk, "proto_", tb.log)
    monitor = ProtocolMonitor(dut, dut.clk, "proto_", tb.log)
    scoreboard = ProtocolScoreboard("Protocol", tb.log)

    # Start monitoring
    await monitor.start_monitoring()

    # Run test sequence
    sequence = BasicSequence(driver, scoreboard)
    await sequence.run()

    # Stop and verify
    await monitor.stop_monitoring()
    assert scoreboard.check_complete(), "Verification failed"

    report = scoreboard.generate_report()
    tb.log.info(report)
```

## Best Practices

### 1. Inherit from TBBase

```python
# Good: Inherit from TBBase
class MyTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        # Get clock management, reset, logging, utilities

# Bad: Start from scratch
class MyTB:
    def __init__(self, dut):
        self.dut = dut
        # Missing all TBBase functionality
```

### 2. Implement Three Mandatory Methods

```python
# Good: All three methods implemented
async def setup_clocks_and_reset(self): ...
async def assert_reset(self): ...
async def deassert_reset(self): ...

# Bad: Missing required methods
# (Only has setup_clocks_and_reset)
```

### 3. Use Field Configurations

```python
# Good: Flexible field configuration
config = GAXIFieldConfig()
config.add_field('addr', addr_width, True)
config.add_field('data', data_width, True)

# Bad: Hardcoded signal access
self.dut.addr.value = 0x1000
self.dut.data.value = 0xDEAD
```

### 4. Create Reusable Components

```python
# Good: Reusable component (>100 lines, used in 3+ tests)
class DataMoverBFM:
    """Reusable data mover protocol driver."""
    # 150+ lines of protocol implementation

# Bad: Duplicate protocol logic in each test
```

### 5. Use Background Monitoring

```python
# Good: Continuous monitoring
async def monitor_outputs(self):
    while self.active:
        await self.wait_clocks('clk', 1)
        if output_valid:
            capture_output()

# Bad: Polling at specific times
# (Misses asynchronous events)
```

## Anti-Patterns to Avoid

### Don't Duplicate Standard Protocols

```python
# ❌ Wrong
class MyAXI4Implementation:
    # 500+ lines reimplementing AXI4

# ✅ Correct
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4MasterWrite
master = AXI4MasterWrite(...)
```

### Don't Skip TBBase Inheritance

```python
# ❌ Wrong
class TestBench:
    def __init__(self, dut):
        self.dut = dut
        # No TBBase features

# ✅ Correct
class TestBench(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
```

### Don't Hardcode Signal Names

```python
# ❌ Wrong
self.dut.m_axi_awaddr.value = addr

# ✅ Correct (use field config and prefix)
master.send({'awaddr': addr})
```

### Don't Create God Classes

```python
# ❌ Wrong: One class does everything
class MegaTestbench:
    # 2000+ lines
    # Driver + Monitor + Scoreboard + Utilities

# ✅ Correct: Separate concerns
class Driver: ...
class Monitor: ...
class Scoreboard: ...
```

## Summary

This guide covered building custom test classes:

1. **TBBase Extension** - Inherit for clock, reset, logging, utilities
2. **Custom Components** - Protocol-specific drivers and monitors
3. **Custom Packets** - Structured data types for complex protocols
4. **Field Configurations** - Flexible signal mapping
5. **Custom Monitors** - Specialized transaction observation
6. **Custom Scoreboards** - Transaction verification
7. **Factory Patterns** - Scalable component creation
8. **Reusable VIP** - Package and distribute verification IP

Key principles:
- Always inherit from TBBase
- Implement three mandatory methods
- Create reusable components (>100 lines, used 3+ times)
- Use field configurations for flexibility
- Apply factory patterns for scalability
- Package VIP for distribution
- Follow framework conventions

---

[Back to Test Tutorial Index](index.md)

---
