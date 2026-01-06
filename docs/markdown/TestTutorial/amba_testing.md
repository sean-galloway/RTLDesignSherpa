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

# AMBA Protocol Testing Tutorial

A comprehensive guide to testing AMBA protocols (AXI4, AXI4-Lite, APB, AXI4-Stream) using the RTL Design Sherpa CocoTB framework, with practical examples for protocol compliance verification, transaction testing, and performance monitoring.

## Table of Contents

- [Overview](#overview)
- [AXI4 Protocol Testing](#axi4-protocol-testing)
- [AXI4-Lite Protocol Testing](#axi4-lite-protocol-testing)
- [APB Protocol Testing](#apb-protocol-testing)
- [AXI4-Stream Protocol Testing](#axi4-stream-protocol-testing)
- [Protocol Compliance Verification](#protocol-compliance-verification)
- [Common Test Patterns](#common-test-patterns)
- [Performance Monitoring](#performance-monitoring)
- [Error Injection and Recovery](#error-injection-and-recovery)
- [Best Practices](#best-practices)
- [Anti-Patterns to Avoid](#anti-patterns-to-avoid)

## Overview

AMBA (Advanced Microcontroller Bus Architecture) protocols are industry-standard interfaces for on-chip communication. The RTL Design Sherpa framework provides comprehensive support for testing all AMBA protocol variants through reusable components in `bin/CocoTBFramework/components/`.

### Framework Components

The framework provides protocol-specific components:

```
bin/CocoTBFramework/components/
├── axi4/              # AXI4 full protocol
│   ├── axi4_interfaces.py        # Master/Slave interfaces
│   ├── axi4_field_configs.py     # Channel configurations
│   ├── axi4_packet.py            # Packet definitions
│   └── axi4_compliance_checker.py # Protocol compliance
├── axi4lite/          # AXI4-Lite simplified protocol
├── apb/               # APB protocol
│   ├── apb_components.py         # Master/Slave drivers
│   └── apb_monitor.py            # Transaction monitoring
├── axis4/             # AXI4-Stream
└── gaxi/              # Generic AXI base classes
```

### Key Principles

1. **Reuse Framework Components** - Don't reimplement standard protocols
2. **Protocol Compliance** - Verify adherence to AMBA specifications
3. **Transaction Verification** - Check data integrity and ordering
4. **Performance Testing** - Measure bandwidth, latency, throughput
5. **Error Handling** - Test error responses and recovery

## AXI4 Protocol Testing

AXI4 is a high-performance, burst-based protocol with separate read and write channels. The framework provides complete AXI4 support through `AXI4MasterRead`, `AXI4MasterWrite`, `AXI4SlaveRead`, and `AXI4SlaveWrite` interfaces.

### Basic AXI4 Read Test

```python
import cocotb
from cocotb.triggers import RisingEdge, Timer
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_interfaces import (
    AXI4MasterRead, AXI4SlaveRead
)

class AXI4ReadTB(TBBase):
    """Testbench for AXI4 read operations."""

    def __init__(self, dut):
        super().__init__(dut)
        self.clk_name = 'aclk'

        # Initialize AXI4 master read interface
        self.axi_master = AXI4MasterRead(
            dut=dut,
            clock=dut.aclk,
            prefix="m_axi_",  # Signal prefix
            data_width=32,
            addr_width=32,
            id_width=8,
            user_width=1,
            log=self.log
        )

        # Initialize memory model for slave behavior
        self.memory = {}

    async def setup_clocks_and_reset(self):
        """Setup clocks and reset sequence."""
        await self.start_clock(self.clk_name, freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        """Assert active-low reset."""
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        """Deassert active-low reset."""
        self.dut.aresetn.value = 1

    async def axi_read_transaction(self, addr, burst_len=0, burst_size=2):
        """
        Execute AXI4 read transaction.

        Args:
            addr: Read address (aligned)
            burst_len: Number of beats - 1 (0-15 for up to 16 beats)
            burst_size: Size encoding (2 = 4 bytes)

        Returns:
            List of read data values
        """
        # Create read address packet
        ar_packet = {
            'arid': 0,
            'araddr': addr,
            'arlen': burst_len,
            'arsize': burst_size,
            'arburst': 1,  # INCR burst type
            'arlock': 0,
            'arcache': 0,
            'arprot': 0,
            'arqos': 0,
            'arregion': 0,
            'aruser': 0
        }

        # Send address phase
        await self.axi_master.ar_channel.send(ar_packet)
        self.log.info(f"Sent AR: addr=0x{addr:08X}, len={burst_len}")

        # Wait for data phase responses
        read_data = []
        for beat in range(burst_len + 1):
            r_packet = await self.axi_master.r_channel.recv()
            read_data.append(r_packet['rdata'])

            # Verify last signal on final beat
            if beat == burst_len:
                assert r_packet['rlast'] == 1, f"RLAST not asserted on final beat"
            else:
                assert r_packet['rlast'] == 0, f"RLAST asserted early at beat {beat}"

            # Check for errors
            assert r_packet['rresp'] == 0, f"Read error: RRESP={r_packet['rresp']}"

        self.log.info(f"Completed read: {len(read_data)} beats")
        return read_data


@cocotb.test()
async def test_axi4_single_read(dut):
    """Test single-beat AXI4 read transaction."""
    tb = AXI4ReadTB(dut)
    await tb.setup_clocks_and_reset()

    # Perform single read
    addr = 0x1000
    data = await tb.axi_read_transaction(addr, burst_len=0)

    assert len(data) == 1, f"Expected 1 beat, got {len(data)}"
    tb.log.info(f"Single read: addr=0x{addr:08X}, data=0x{data[0]:08X}")


@cocotb.test()
async def test_axi4_burst_read(dut):
    """Test multi-beat AXI4 burst read."""
    tb = AXI4ReadTB(dut)
    await tb.setup_clocks_and_reset()

    # Test different burst lengths
    test_cases = [
        (0x2000, 1),   # 2 beats
        (0x3000, 3),   # 4 beats
        (0x4000, 7),   # 8 beats
        (0x5000, 15),  # 16 beats (maximum)
    ]

    for addr, burst_len in test_cases:
        data = await tb.axi_read_transaction(addr, burst_len=burst_len)
        expected_beats = burst_len + 1
        assert len(data) == expected_beats, \
            f"Burst length {burst_len}: expected {expected_beats} beats, got {len(data)}"
        tb.log.info(f"Burst read: addr=0x{addr:08X}, beats={expected_beats}")
```

### AXI4 Write Test

```python
class AXI4WriteTB(TBBase):
    """Testbench for AXI4 write operations."""

    def __init__(self, dut):
        super().__init__(dut)
        self.clk_name = 'aclk'

        from CocoTBFramework.components.axi4.axi4_interfaces import AXI4MasterWrite

        self.axi_master = AXI4MasterWrite(
            dut=dut,
            clock=dut.aclk,
            prefix="m_axi_",
            data_width=32,
            addr_width=32,
            id_width=8,
            user_width=1,
            log=self.log
        )

    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 5)

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def axi_write_transaction(self, addr, data_list, burst_size=2):
        """
        Execute AXI4 write transaction.

        Args:
            addr: Write address
            data_list: List of data values to write
            burst_size: Size encoding (2 = 4 bytes)
        """
        burst_len = len(data_list) - 1

        # Address phase
        aw_packet = {
            'awid': 0,
            'awaddr': addr,
            'awlen': burst_len,
            'awsize': burst_size,
            'awburst': 1,  # INCR
            'awlock': 0,
            'awcache': 0,
            'awprot': 0,
            'awqos': 0,
            'awregion': 0,
            'awuser': 0
        }

        await self.axi_master.aw_channel.send(aw_packet)
        self.log.info(f"Sent AW: addr=0x{addr:08X}, len={burst_len}")

        # Data phase
        for i, data_value in enumerate(data_list):
            w_packet = {
                'wdata': data_value,
                'wstrb': 0xF,  # All bytes valid
                'wlast': 1 if i == burst_len else 0,
                'wuser': 0
            }
            await self.axi_master.w_channel.send(w_packet)

        # Wait for write response
        b_packet = await self.axi_master.b_channel.recv()
        assert b_packet['bresp'] == 0, f"Write error: BRESP={b_packet['bresp']}"

        self.log.info(f"Write complete: {len(data_list)} beats")


@cocotb.test()
async def test_axi4_write_read_verify(dut):
    """Test AXI4 write followed by read-back verification."""
    from CocoTBFramework.components.axi4.axi4_interfaces import (
        AXI4MasterWrite, AXI4MasterRead
    )

    tb_write = AXI4WriteTB(dut)
    tb_read = AXI4ReadTB(dut)

    await tb_write.setup_clocks_and_reset()

    # Write test data
    addr = 0x8000
    write_data = [0xDEADBEEF, 0xCAFEBABE, 0x12345678, 0xABCDEF00]

    await tb_write.axi_write_transaction(addr, write_data)

    # Read back and verify
    read_data = await tb_read.axi_read_transaction(addr, burst_len=len(write_data)-1)

    assert read_data == write_data, \
        f"Data mismatch: write={write_data}, read={read_data}"

    tb_write.log.info("Write-read verification PASSED")
```

### Outstanding Transactions Test

```python
@cocotb.test()
async def test_axi4_outstanding_reads(dut):
    """Test multiple outstanding read transactions."""
    tb = AXI4ReadTB(dut)
    await tb.setup_clocks_and_reset()

    # Issue multiple read requests without waiting for data
    addresses = [0x1000, 0x2000, 0x3000, 0x4000]

    # Send all address requests
    for addr in addresses:
        ar_packet = {
            'arid': addresses.index(addr),  # Unique ID per transaction
            'araddr': addr,
            'arlen': 0,  # Single beat
            'arsize': 2,
            'arburst': 1,
            'arlock': 0,
            'arcache': 0,
            'arprot': 0,
            'arqos': 0,
            'arregion': 0,
            'aruser': 0
        }
        await tb.axi_master.ar_channel.send(ar_packet)
        tb.log.info(f"Issued read {addresses.index(addr)}: addr=0x{addr:08X}")

    # Collect all responses (may arrive out of order)
    responses = {}
    for _ in range(len(addresses)):
        r_packet = await tb.axi_master.r_channel.recv()
        rid = r_packet['rid']
        responses[rid] = r_packet['rdata']
        tb.log.info(f"Received response {rid}: data=0x{r_packet['rdata']:08X}")

    # Verify all transactions completed
    assert len(responses) == len(addresses), \
        f"Expected {len(addresses)} responses, got {len(responses)}"

    tb.log.info(f"Outstanding transactions test PASSED: {len(addresses)} transactions")
```

## AXI4-Lite Protocol Testing

AXI4-Lite is a simplified subset of AXI4 for register access. It doesn't support bursts, has narrower ID widths, and simpler handshaking.

### Basic AXI4-Lite Test

```python
from CocoTBFramework.components.axil4.axil4_interfaces import (
    AXIL4MasterRead, AXIL4MasterWrite
)

class AXIL4TB(TBBase):
    """Testbench for AXI4-Lite register access."""

    def __init__(self, dut):
        super().__init__(dut)
        self.clk_name = 'aclk'

        self.axil_master = AXIL4MasterWrite(
            dut=dut,
            clock=dut.aclk,
            prefix="s_axil_",
            data_width=32,
            addr_width=32,
            log=self.log
        )

    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def write_register(self, addr, data):
        """Write to AXI4-Lite register."""
        aw_packet = {'awaddr': addr, 'awprot': 0}
        w_packet = {'wdata': data, 'wstrb': 0xF}

        await self.axil_master.aw_channel.send(aw_packet)
        await self.axil_master.w_channel.send(w_packet)

        b_packet = await self.axil_master.b_channel.recv()
        assert b_packet['bresp'] == 0, f"Write error at addr=0x{addr:08X}"

    async def read_register(self, addr):
        """Read from AXI4-Lite register."""
        ar_packet = {'araddr': addr, 'arprot': 0}

        await self.axil_master.ar_channel.send(ar_packet)
        r_packet = await self.axil_master.r_channel.recv()

        assert r_packet['rresp'] == 0, f"Read error at addr=0x{addr:08X}"
        return r_packet['rdata']


@cocotb.test()
async def test_axil4_register_access(dut):
    """Test AXI4-Lite register read/write."""
    tb = AXIL4TB(dut)
    await tb.setup_clocks_and_reset()

    # Register map test
    registers = {
        0x00: 0x12345678,  # Control register
        0x04: 0xABCDEF00,  # Status register
        0x08: 0xDEADBEEF,  # Data register
    }

    # Write all registers
    for addr, data in registers.items():
        await tb.write_register(addr, data)
        tb.log.info(f"Wrote 0x{data:08X} to 0x{addr:04X}")

    # Read back and verify
    for addr, expected_data in registers.items():
        read_data = await tb.read_register(addr)
        assert read_data == expected_data, \
            f"Register 0x{addr:04X}: expected 0x{expected_data:08X}, got 0x{read_data:08X}"
        tb.log.info(f"Verified 0x{addr:04X}: 0x{read_data:08X}")
```

## APB Protocol Testing

APB (Advanced Peripheral Bus) is a simple, low-bandwidth protocol for peripheral access. The framework provides `APBMaster` and `APBSlave` components.

### Basic APB Test

```python
from CocoTBFramework.components.apb.apb_components import APBMaster

class APBTB(TBBase):
    """Testbench for APB peripheral access."""

    def __init__(self, dut):
        super().__init__(dut)
        self.clk_name = 'pclk'

        self.apb_master = APBMaster(
            dut=dut,
            clock=dut.pclk,
            prefix="apb_",
            addr_width=16,
            data_width=32,
            log=self.log
        )

    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()

    async def assert_reset(self):
        self.dut.presetn.value = 0

    async def deassert_reset(self):
        self.dut.presetn.value = 1

    async def apb_write(self, addr, data):
        """Write via APB."""
        await self.apb_master.write(addr, data)
        self.log.info(f"APB write: addr=0x{addr:04X}, data=0x{data:08X}")

    async def apb_read(self, addr):
        """Read via APB."""
        data = await self.apb_master.read(addr)
        self.log.info(f"APB read: addr=0x{addr:04X}, data=0x{data:08X}")
        return data


@cocotb.test()
async def test_apb_basic_access(dut):
    """Test basic APB read/write operations."""
    tb = APBTB(dut)
    await tb.setup_clocks_and_reset()

    # Test write-read sequence
    test_data = [
        (0x0000, 0x11111111),
        (0x0004, 0x22222222),
        (0x0008, 0x33333333),
        (0x000C, 0x44444444),
    ]

    for addr, data in test_data:
        await tb.apb_write(addr, data)
        read_data = await tb.apb_read(addr)
        assert read_data == data, \
            f"APB mismatch at 0x{addr:04X}: wrote 0x{data:08X}, read 0x{read_data:08X}"
```

### APB Timing Test

```python
@cocotb.test()
async def test_apb_wait_states(dut):
    """Test APB with PREADY wait states."""
    tb = APBTB(dut)
    await tb.setup_clocks_and_reset()

    # Configure slave to insert wait states
    await tb.apb_write(0x0100, 0x5)  # 5 cycle wait state

    # Measure transaction duration
    start_time = cocotb.utils.get_sim_time(units='ns')

    await tb.apb_write(0x0200, 0xTESTDATA)

    end_time = cocotb.utils.get_sim_time(units='ns')
    duration = end_time - start_time

    # Verify wait states were inserted
    expected_cycles = 2 + 5  # Setup + access + wait states
    expected_duration = expected_cycles * 10  # 10ns clock period

    assert duration >= expected_duration, \
        f"Transaction too fast: {duration}ns vs expected {expected_duration}ns"

    tb.log.info(f"APB wait state test PASSED: {duration}ns")
```

## AXI4-Stream Protocol Testing

AXI4-Stream is a point-to-point streaming protocol. The framework provides `AXIS4Master` and `AXIS4Slave` for streaming data.

### Basic AXIS4 Test

```python
from CocoTBFramework.components.axis4.axis4_master import AXIS4Master
from CocoTBFramework.components.axis4.axis4_slave import AXIS4Slave

class AXIS4TB(TBBase):
    """Testbench for AXI4-Stream."""

    def __init__(self, dut):
        super().__init__(dut)
        self.clk_name = 'aclk'

        self.axis_master = AXIS4Master(
            dut=dut,
            clock=dut.aclk,
            prefix="s_axis_",
            data_width=32,
            log=self.log
        )

        self.axis_slave = AXIS4Slave(
            dut=dut,
            clock=dut.aclk,
            prefix="m_axis_",
            data_width=32,
            log=self.log
        )

    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1


@cocotb.test()
async def test_axis4_streaming(dut):
    """Test AXI4-Stream data transfer."""
    tb = AXIS4TB(dut)
    await tb.setup_clocks_and_reset()

    # Send stream of data
    test_data = [0x100 + i for i in range(16)]

    for i, data in enumerate(test_data):
        packet = {
            'tdata': data,
            'tkeep': 0xF,  # All bytes valid
            'tlast': 1 if i == len(test_data)-1 else 0,
            'tuser': 0
        }
        await tb.axis_master.send(packet)

    # Receive and verify
    received_data = []
    for i in range(len(test_data)):
        packet = await tb.axis_slave.recv()
        received_data.append(packet['tdata'])

        # Verify TLAST on final packet
        if i == len(test_data) - 1:
            assert packet['tlast'] == 1, "TLAST not asserted on final packet"

    assert received_data == test_data, \
        f"Data mismatch: sent={test_data}, received={received_data}"

    tb.log.info(f"AXIS4 streaming test PASSED: {len(test_data)} packets")
```

### AXIS4 Backpressure Test

```python
@cocotb.test()
async def test_axis4_backpressure(dut):
    """Test AXI4-Stream with backpressure."""
    tb = AXIS4TB(dut)
    await tb.setup_clocks_and_reset()

    # Configure slave to apply backpressure
    tb.axis_slave.set_backpressure_mode('random', probability=0.5)

    # Send data stream
    num_packets = 100
    for i in range(num_packets):
        packet = {
            'tdata': 0x1000 + i,
            'tkeep': 0xF,
            'tlast': 1 if i == num_packets-1 else 0,
            'tuser': 0
        }
        await tb.axis_master.send(packet)

    # Receive with backpressure
    received_count = 0
    for i in range(num_packets):
        packet = await tb.axis_slave.recv()
        received_count += 1

    assert received_count == num_packets, \
        f"Packet loss: sent {num_packets}, received {received_count}"

    tb.log.info(f"Backpressure test PASSED: {received_count} packets")
```

## Protocol Compliance Verification

The framework includes compliance checkers to verify protocol adherence according to AMBA specifications.

### AXI4 Compliance Checking

```python
from CocoTBFramework.components.axi4.axi4_compliance_checker import AXI4ComplianceChecker

@cocotb.test()
async def test_axi4_compliance(dut):
    """Test AXI4 protocol compliance."""
    tb = AXI4ReadTB(dut)
    await tb.setup_clocks_and_reset()

    # Enable compliance checker
    compliance = AXI4ComplianceChecker(
        dut=dut,
        clock=dut.aclk,
        prefix="m_axi_",
        log=tb.log
    )

    # Start compliance monitoring
    cocotb.start_soon(compliance.monitor())

    # Run test transactions
    for i in range(20):
        addr = 0x1000 + (i * 0x100)
        await tb.axi_read_transaction(addr, burst_len=3)

    # Check for violations
    violations = compliance.get_violations()
    assert len(violations) == 0, \
        f"Protocol violations detected: {violations}"

    tb.log.info("AXI4 compliance test PASSED: no violations")
```

### Common Protocol Violations

```python
@cocotb.test()
async def test_protocol_violation_detection(dut):
    """Verify compliance checker detects violations."""
    tb = AXI4ReadTB(dut)
    await tb.setup_clocks_and_reset()

    compliance = AXI4ComplianceChecker(dut, dut.aclk, "m_axi_", tb.log)
    cocotb.start_soon(compliance.monitor())

    # Intentionally violate protocol (address not aligned)
    ar_packet = {
        'arid': 0,
        'araddr': 0x1003,  # Misaligned for 4-byte access
        'arlen': 0,
        'arsize': 2,  # 4 bytes
        'arburst': 1,
        # ... other fields
    }

    await tb.axi_master.ar_channel.send(ar_packet)
    await tb.wait_clocks('aclk', 10)

    # Check that violation was detected
    violations = compliance.get_violations()
    assert any('alignment' in v.lower() for v in violations), \
        "Address alignment violation not detected"
```

## Common Test Patterns

### Pattern: Burst Transaction Testing

```python
@cocotb.test()
async def test_burst_variants(dut):
    """Test different burst types and sizes."""
    tb = AXI4ReadTB(dut)
    await tb.setup_clocks_and_reset()

    # Test matrix: burst type x burst length x burst size
    test_cases = [
        # (burst_type, burst_len, burst_size, description)
        (1, 0, 0, "INCR 1-beat 1-byte"),
        (1, 0, 1, "INCR 1-beat 2-byte"),
        (1, 0, 2, "INCR 1-beat 4-byte"),
        (1, 3, 2, "INCR 4-beat 4-byte"),
        (1, 15, 2, "INCR 16-beat 4-byte"),
        (2, 3, 2, "WRAP 4-beat 4-byte"),
        (2, 7, 2, "WRAP 8-beat 4-byte"),
    ]

    for burst_type, burst_len, burst_size, description in test_cases:
        addr = 0x10000

        ar_packet = {
            'arid': 0,
            'araddr': addr,
            'arlen': burst_len,
            'arsize': burst_size,
            'arburst': burst_type,
            # ... other fields
        }

        await tb.axi_master.ar_channel.send(ar_packet)

        # Collect responses
        for beat in range(burst_len + 1):
            r_packet = await tb.axi_master.r_channel.recv()

        tb.log.info(f"Burst test PASSED: {description}")
```

### Pattern: Outstanding Transaction Ordering

```python
@cocotb.test()
async def test_transaction_ordering(dut):
    """Test that responses can arrive out of order."""
    tb = AXI4ReadTB(dut)
    await tb.setup_clocks_and_reset()

    # Issue multiple transactions with different IDs
    num_transactions = 8
    for tid in range(num_transactions):
        ar_packet = {
            'arid': tid,
            'araddr': 0x1000 + (tid * 0x100),
            'arlen': 0,
            'arsize': 2,
            'arburst': 1,
            # ... other fields
        }
        await tb.axi_master.ar_channel.send(ar_packet)

    # Collect responses and track ordering
    response_order = []
    for _ in range(num_transactions):
        r_packet = await tb.axi_master.r_channel.recv()
        response_order.append(r_packet['rid'])

    # Verify all IDs received
    assert sorted(response_order) == list(range(num_transactions)), \
        f"Missing transaction IDs: {response_order}"

    # Log if reordering occurred
    if response_order != list(range(num_transactions)):
        tb.log.info(f"Transaction reordering detected: {response_order}")
    else:
        tb.log.info("Transactions completed in order")
```

### Pattern: Backpressure Testing

```python
@cocotb.test()
async def test_backpressure_scenarios(dut):
    """Test various backpressure conditions."""
    tb = AXI4ReadTB(dut)
    await tb.setup_clocks_and_reset()

    import random

    # Test with different backpressure profiles
    profiles = [
        {'name': 'No backpressure', 'ready_prob': 1.0},
        {'name': 'Light backpressure', 'ready_prob': 0.8},
        {'name': 'Heavy backpressure', 'ready_prob': 0.3},
        {'name': 'Bursty backpressure', 'ready_prob': 'alternating'},
    ]

    for profile in profiles:
        tb.log.info(f"Testing: {profile['name']}")

        # Configure backpressure behavior
        if profile['ready_prob'] == 'alternating':
            # Alternate between ready and not ready
            tb.axi_master.r_channel.set_ready_mode('alternating')
        else:
            tb.axi_master.r_channel.set_ready_probability(profile['ready_prob'])

        # Run transactions
        for i in range(10):
            await tb.axi_read_transaction(0x2000 + i*16, burst_len=3)

        tb.log.info(f"Profile '{profile['name']}' PASSED")
```

## Performance Monitoring

### Bandwidth Measurement

```python
@cocotb.test()
async def test_bandwidth_measurement(dut):
    """Measure AXI4 bandwidth."""
    tb = AXI4WriteTB(dut)
    await tb.setup_clocks_and_reset()

    # Configuration
    data_width_bytes = 4  # 32-bit data bus
    num_transactions = 100
    burst_len = 15  # 16 beats per transaction

    # Start timing
    start_time = cocotb.utils.get_sim_time(units='ns')

    # Execute transactions
    for i in range(num_transactions):
        addr = 0x80000000 + (i * 64)
        data = [0xDATA0000 + j for j in range(burst_len + 1)]
        await tb.axi_write_transaction(addr, data)

    # End timing
    end_time = cocotb.utils.get_sim_time(units='ns')
    duration_ns = end_time - start_time

    # Calculate bandwidth
    total_bytes = num_transactions * (burst_len + 1) * data_width_bytes
    bandwidth_mbps = (total_bytes * 1000) / duration_ns  # MB/s

    # Calculate efficiency
    clock_freq_mhz = 100  # 10ns period
    theoretical_max = clock_freq_mhz * data_width_bytes  # MB/s
    efficiency = (bandwidth_mbps / theoretical_max) * 100

    tb.log.info(f"Bandwidth: {bandwidth_mbps:.2f} MB/s")
    tb.log.info(f"Efficiency: {efficiency:.1f}%")
    tb.log.info(f"Theoretical max: {theoretical_max:.2f} MB/s")

    # Verify acceptable performance
    assert efficiency > 70, f"Bandwidth efficiency too low: {efficiency:.1f}%"
```

### Latency Measurement

```python
@cocotb.test()
async def test_latency_measurement(dut):
    """Measure transaction latency."""
    tb = AXI4ReadTB(dut)
    await tb.setup_clocks_and_reset()

    latencies = []

    for i in range(50):
        # Measure single transaction latency
        start = cocotb.utils.get_sim_time(units='ns')

        await tb.axi_read_transaction(0x1000 + i*16, burst_len=0)

        end = cocotb.utils.get_sim_time(units='ns')
        latencies.append(end - start)

    # Calculate statistics
    avg_latency = sum(latencies) / len(latencies)
    min_latency = min(latencies)
    max_latency = max(latencies)

    tb.log.info(f"Latency statistics:")
    tb.log.info(f"  Average: {avg_latency:.1f} ns")
    tb.log.info(f"  Minimum: {min_latency:.1f} ns")
    tb.log.info(f"  Maximum: {max_latency:.1f} ns")

    # Verify latency requirements
    assert max_latency < 500, f"Maximum latency too high: {max_latency:.1f}ns"
```

## Error Injection and Recovery

### Testing Error Responses

```python
@cocotb.test()
async def test_error_responses(dut):
    """Test error response handling."""
    tb = AXI4ReadTB(dut)
    await tb.setup_clocks_and_reset()

    # Configure slave to return errors for certain addresses
    error_addr = 0xBAD0000

    ar_packet = {
        'arid': 0,
        'araddr': error_addr,
        'arlen': 0,
        'arsize': 2,
        'arburst': 1,
        # ... other fields
    }

    await tb.axi_master.ar_channel.send(ar_packet)

    # Receive error response
    r_packet = await tb.axi_master.r_channel.recv()

    # Verify error response
    assert r_packet['rresp'] != 0, \
        f"Expected error response at addr=0x{error_addr:08X}"

    # Log error type
    resp_types = {0: 'OKAY', 1: 'EXOKAY', 2: 'SLVERR', 3: 'DECERR'}
    tb.log.info(f"Error response: {resp_types.get(r_packet['rresp'], 'UNKNOWN')}")

    # Verify system continues operating after error
    normal_addr = 0x1000
    await tb.axi_read_transaction(normal_addr, burst_len=0)
    tb.log.info("System recovered from error response")
```

### Timeout Testing

```python
@cocotb.test()
async def test_timeout_detection(dut):
    """Test timeout detection and handling."""
    tb = AXI4ReadTB(dut)
    await tb.setup_clocks_and_reset()

    # Disable slave response to force timeout
    # (Implementation depends on testbench structure)

    timeout_occurred = False

    try:
        # Attempt transaction with timeout
        await cocotb.triggers.with_timeout(
            tb.axi_read_transaction(0x1000),
            timeout_time=1000,
            timeout_unit='ns'
        )
    except cocotb.triggers.TimeoutError:
        timeout_occurred = True
        tb.log.info("Timeout detected as expected")

    assert timeout_occurred, "Timeout should have occurred but didn't"
```

## Best Practices

### 1. Use Framework Components

```python
# Good: Use framework AXI4 components
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4MasterRead

self.axi_master = AXI4MasterRead(dut, clock, prefix="m_axi_", ...)

# Bad: Reimplement AXI4 protocol
class MyCustomAXI4:  # Don't do this!
    async def send_ar(...):  # Framework already provides this
```

### 2. Verify Protocol Compliance

```python
# Good: Always enable compliance checking
compliance = AXI4ComplianceChecker(dut, clock, prefix, log)
cocotb.start_soon(compliance.monitor())

# Run tests...

violations = compliance.get_violations()
assert len(violations) == 0, f"Violations: {violations}"
```

### 3. Test Edge Cases

```python
# Test boundary conditions
test_cases = [
    (0x00000000, "Minimum address"),
    (0xFFFFFFFC, "Maximum aligned address"),
    (0x00000000, "Zero-length burst"),  # Invalid - should error
    (0x1000, "4KB boundary crossing"),
]
```

### 4. Measure Performance

```python
# Always include performance metrics
start_time = cocotb.utils.get_sim_time(units='ns')
# ... run transactions ...
end_time = cocotb.utils.get_sim_time(units='ns')

bandwidth = calculate_bandwidth(bytes_transferred, end_time - start_time)
log.info(f"Achieved bandwidth: {bandwidth:.2f} MB/s")
```

### 5. Test Error Conditions

```python
# Test error paths
error_scenarios = [
    ('SLVERR', 0xBADADDR),
    ('DECERR', 0xNODECODE),
]

for error_type, addr in error_scenarios:
    response = await send_transaction(addr)
    assert response['resp'] != 0, f"Expected {error_type}"
```

## Anti-Patterns to Avoid

### Don't Reimplement Standard Protocols

```python
# ❌ Wrong: Reimplementing AXI4
class MyAXI4Implementation:
    async def write_transaction(self, addr, data):
        # 500+ lines of AXI4 protocol...

# ✅ Correct: Use framework components
from CocoTBFramework.components.axi4.axi4_interfaces import AXI4MasterWrite
master = AXI4MasterWrite(dut, clock, prefix, ...)
```

### Don't Skip Compliance Checking

```python
# ❌ Wrong: No compliance verification
await tb.axi_read_transaction(addr)
# Hope protocol is correct...

# ✅ Correct: Enable compliance checking
compliance = AXI4ComplianceChecker(dut, clock, prefix, log)
cocotb.start_soon(compliance.monitor())
await tb.axi_read_transaction(addr)
violations = compliance.get_violations()
assert len(violations) == 0
```

### Don't Ignore Backpressure

```python
# ❌ Wrong: Assume immediate ready
self.dut.tready.value = 1  # Always ready - unrealistic

# ✅ Correct: Test with realistic backpressure
slave.set_backpressure_mode('random', probability=0.7)
```

### Don't Test Only Happy Paths

```python
# ❌ Wrong: Only test successful transactions
await write(0x1000, 0xDATA)
await read(0x1000)  # Only success case

# ✅ Correct: Test error cases too
await test_slave_error_response()
await test_decode_error()
await test_timeout_handling()
```

### Don't Hardcode Timing

```python
# ❌ Wrong: Hardcoded delays
await Timer(100, units='ns')  # Magic number

# ✅ Correct: Use clock cycles
await tb.wait_clocks('aclk', 10)  # Clear intent
```

## Summary

This tutorial covered comprehensive AMBA protocol testing using the RTL Design Sherpa CocoTB framework:

1. **AXI4** - Full protocol with burst support and outstanding transactions
2. **AXI4-Lite** - Simplified register access protocol
3. **APB** - Low-bandwidth peripheral bus
4. **AXI4-Stream** - Point-to-point streaming protocol
5. **Compliance** - Protocol adherence verification
6. **Patterns** - Bursts, ordering, backpressure
7. **Performance** - Bandwidth and latency measurement
8. **Errors** - Error injection and recovery testing

Key takeaways:
- Reuse framework components (don't reimplement protocols)
- Always verify protocol compliance
- Test both success and error paths
- Measure performance metrics
- Use realistic timing and backpressure

---

[Back to Test Tutorial Index](index.md)

---
