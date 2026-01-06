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

# System Level Testing Guide

A comprehensive guide to system-level integration testing using the RTL Design Sherpa CocoTB framework, covering multi-protocol environments, end-to-end verification, system scoreboards, regression organization, and performance characterization.

## Table of Contents

- [Overview](#overview)
- [System Testing Philosophy](#system-testing-philosophy)
- [Multi-Protocol Integration](#multi-protocol-integration)
- [End-to-End Data Path Verification](#end-to-end-data-path-verification)
- [System-Level Scoreboards](#system-level-scoreboards)
- [Test Scenarios and Use Cases](#test-scenarios-and-use-cases)
- [Regression Test Organization](#regression-test-organization)
- [Performance Characterization](#performance-characterization)
- [Debug and Analysis](#debug-and-analysis)
- [Best Practices](#best-practices)
- [Anti-Patterns to Avoid](#anti-patterns-to-avoid)

## Overview

System-level testing validates the complete RTL design by verifying interactions between multiple components, protocols, and subsystems. Unlike unit tests that focus on individual modules, system tests ensure the entire system functions correctly under realistic operating conditions.

### System Testing Goals

1. **Integration Verification** - Ensure components work together correctly
2. **Protocol Interoperability** - Verify multi-protocol communication
3. **End-to-End Functionality** - Validate complete data paths
4. **Performance Validation** - Measure system-level metrics
5. **Stress Testing** - Verify operation under load
6. **Real-World Scenarios** - Test use cases and applications

### Framework Support

The RTL Design Sherpa framework provides system-level testing infrastructure:

```
bin/CocoTBFramework/
├── components/           # Protocol BFMs (AXI4, APB, AXIS, etc.)
├── tbclasses/           # Reusable testbenches
│   └── shared/          # TBBase and utilities
└── scoreboards/         # System verification components
    ├── generic/         # Protocol-agnostic scoreboards
    └── [protocol]/      # Protocol-specific scoreboards
```

## System Testing Philosophy

### Layered Verification Approach

System testing follows a hierarchical verification strategy:

```
┌─────────────────────────────────────────┐
│ System Tests (End-to-End)               │  ← Full system scenarios
├─────────────────────────────────────────┤
│ Integration Tests (Multi-Component)     │  ← Subsystem interactions
├─────────────────────────────────────────┤
│ Unit Tests (Single Module)              │  ← Component verification
└─────────────────────────────────────────┘
```

### Test Complexity Levels

The framework supports multiple test complexity levels:

```python
# Define test levels
test_levels = {
    'basic': {
        'operations': 10,
        'protocols': ['axi4'],
        'scenarios': ['simple_transfer'],
        'duration': '~30s'
    },
    'medium': {
        'operations': 50,
        'protocols': ['axi4', 'apb'],
        'scenarios': ['concurrent_access', 'multi_master'],
        'duration': '~2min'
    },
    'full': {
        'operations': 200,
        'protocols': ['axi4', 'apb', 'axis4'],
        'scenarios': ['stress_test', 'corner_cases', 'error_injection'],
        'duration': '~5min'
    }
}
```

### Key Principles

1. **Realistic Traffic** - Use representative access patterns
2. **Concurrent Operations** - Test parallel protocol activity
3. **Complete Data Paths** - Verify end-to-end data integrity
4. **System Monitors** - Observe all critical interfaces
5. **Performance Metrics** - Measure system-level characteristics
6. **Comprehensive Coverage** - Exercise all system features

## Multi-Protocol Integration

Real systems use multiple protocols simultaneously. System tests must verify these protocols interact correctly.

### Basic Multi-Protocol System

```python
import cocotb
from cocotb.triggers import RisingEdge, Timer
from CocoTBFramework.tbclasses.shared.tbbase import TBBase
from CocoTBFramework.components.axi4.axi4_interfaces import (
    AXI4MasterWrite, AXI4MasterRead
)
from CocoTBFramework.components.apb.apb_components import APBMaster
from CocoTBFramework.components.axis4.axis4_master import AXIS4Master
from CocoTBFramework.components.axis4.axis4_slave import AXIS4Slave

class SystemTB(TBBase):
    """
    System-level testbench integrating AXI4, APB, and AXIS4 protocols.

    System Architecture:
        AXI4 Master → DMA Controller → Memory
        APB Master → Configuration Registers
        AXIS4 → Streaming Data Path
    """

    def __init__(self, dut):
        super().__init__(dut)
        self.clk_name = 'aclk'

        # AXI4 Memory Interface
        self.axi_mem_write = AXI4MasterWrite(
            dut=dut,
            clock=dut.aclk,
            prefix="m_axi_mem_",
            data_width=64,
            addr_width=32,
            id_width=4,
            log=self.log
        )

        self.axi_mem_read = AXI4MasterRead(
            dut=dut,
            clock=dut.aclk,
            prefix="m_axi_mem_",
            data_width=64,
            addr_width=32,
            id_width=4,
            log=self.log
        )

        # APB Configuration Interface
        self.apb_config = APBMaster(
            dut=dut,
            clock=dut.aclk,
            prefix="apb_",
            addr_width=16,
            data_width=32,
            log=self.log
        )

        # AXIS4 Streaming Interface
        self.axis_input = AXIS4Master(
            dut=dut,
            clock=dut.aclk,
            prefix="s_axis_",
            data_width=64,
            log=self.log
        )

        self.axis_output = AXIS4Slave(
            dut=dut,
            clock=dut.aclk,
            prefix="m_axis_",
            data_width=64,
            log=self.log
        )

        # System state tracking
        self.memory_model = {}
        self.config_registers = {}
        self.transaction_log = []

    async def setup_clocks_and_reset(self):
        """Initialize system clocks and reset."""
        await self.start_clock(self.clk_name, freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 20)
        await self.deassert_reset()
        await self.wait_clocks(self.clk_name, 10)
        self.log.info("System reset complete")

    async def assert_reset(self):
        """Assert all reset signals."""
        self.dut.aresetn.value = 0
        self.dut.presetn.value = 0

    async def deassert_reset(self):
        """Release all reset signals."""
        self.dut.aresetn.value = 1
        self.dut.presetn.value = 1

    async def configure_system(self, config_dict):
        """
        Configure system via APB interface.

        Args:
            config_dict: Dictionary of {register_addr: value}
        """
        self.log.info("Configuring system via APB")

        for addr, value in config_dict.items():
            await self.apb_config.write(addr, value)
            self.config_registers[addr] = value
            self.log.debug(f"Config[0x{addr:04X}] = 0x{value:08X}")

        # Verify configuration
        for addr, expected in config_dict.items():
            read_val = await self.apb_config.read(addr)
            assert read_val == expected, \
                f"Config verify failed: addr=0x{addr:04X}, expected=0x{expected:08X}, got=0x{read_val:08X}"

        self.log.info(f"System configured: {len(config_dict)} registers")

    async def dma_transfer(self, src_addr, dst_addr, length):
        """
        Perform DMA transfer using AXI4 interface.

        Args:
            src_addr: Source memory address
            dst_addr: Destination memory address
            length: Transfer length in bytes
        """
        self.log.info(f"DMA transfer: 0x{src_addr:08X} → 0x{dst_addr:08X}, {length} bytes")

        # Read from source
        read_data = await self.axi_read_burst(src_addr, length)

        # Write to destination
        await self.axi_write_burst(dst_addr, read_data)

        # Log transaction
        self.transaction_log.append({
            'type': 'dma',
            'src': src_addr,
            'dst': dst_addr,
            'length': length,
            'data': read_data
        })

        return read_data

    async def axi_read_burst(self, addr, num_bytes):
        """Read data via AXI4 with automatic burst handling."""
        data_width_bytes = 8  # 64-bit interface
        num_beats = (num_bytes + data_width_bytes - 1) // data_width_bytes

        # Send read address
        ar_packet = {
            'arid': 0,
            'araddr': addr,
            'arlen': num_beats - 1,
            'arsize': 3,  # 8 bytes
            'arburst': 1,  # INCR
            'arlock': 0,
            'arcache': 0,
            'arprot': 0,
            'arqos': 0,
            'arregion': 0,
            'aruser': 0
        }

        await self.axi_mem_read.ar_channel.send(ar_packet)

        # Collect read data
        read_data = []
        for beat in range(num_beats):
            r_packet = await self.axi_mem_read.r_channel.recv()
            read_data.append(r_packet['rdata'])

            assert r_packet['rresp'] == 0, f"Read error at beat {beat}"
            if beat == num_beats - 1:
                assert r_packet['rlast'] == 1, "RLAST not asserted"

        return read_data

    async def axi_write_burst(self, addr, data_list):
        """Write data via AXI4 with automatic burst handling."""
        num_beats = len(data_list)

        # Send write address
        aw_packet = {
            'awid': 0,
            'awaddr': addr,
            'awlen': num_beats - 1,
            'awsize': 3,  # 8 bytes
            'awburst': 1,  # INCR
            'awlock': 0,
            'awcache': 0,
            'awprot': 0,
            'awqos': 0,
            'awregion': 0,
            'awuser': 0
        }

        await self.axi_mem_write.aw_channel.send(aw_packet)

        # Send write data
        for i, data in enumerate(data_list):
            w_packet = {
                'wdata': data,
                'wstrb': 0xFF,  # All bytes valid
                'wlast': 1 if i == num_beats - 1 else 0,
                'wuser': 0
            }
            await self.axi_mem_write.w_channel.send(w_packet)

        # Wait for write response
        b_packet = await self.axi_mem_write.b_channel.recv()
        assert b_packet['bresp'] == 0, f"Write error: BRESP={b_packet['bresp']}"

    async def stream_data(self, data_list):
        """
        Send data through AXIS4 streaming interface.

        Args:
            data_list: List of data values to stream

        Returns:
            List of received data from output stream
        """
        self.log.info(f"Streaming {len(data_list)} packets")

        # Start background receiver
        received_data = []
        receive_complete = False

        async def receive_stream():
            nonlocal received_data, receive_complete
            for i in range(len(data_list)):
                packet = await self.axis_output.recv()
                received_data.append(packet['tdata'])
                if packet['tlast']:
                    self.log.debug(f"Received TLAST at packet {i}")
            receive_complete = True

        # Start receiver task
        recv_task = cocotb.start_soon(receive_stream())

        # Send data stream
        for i, data in enumerate(data_list):
            packet = {
                'tdata': data,
                'tkeep': 0xFF,
                'tlast': 1 if i == len(data_list) - 1 else 0,
                'tuser': 0
            }
            await self.axis_input.send(packet)
            await self.wait_clocks(self.clk_name, 1)

        # Wait for reception to complete
        timeout = 1000
        cycles = 0
        while not receive_complete and cycles < timeout:
            await self.wait_clocks(self.clk_name, 1)
            cycles += 1

        assert receive_complete, "Stream reception timeout"
        self.log.info(f"Stream transfer complete: {len(received_data)} packets")

        return received_data


@cocotb.test()
async def test_multi_protocol_operation(dut):
    """Test concurrent multi-protocol operation."""
    tb = SystemTB(dut)
    await tb.setup_clocks_and_reset()

    # 1. Configure system via APB
    config = {
        0x0000: 0x00000001,  # Enable DMA
        0x0004: 0x00001000,  # DMA source address
        0x0008: 0x00002000,  # DMA destination address
        0x000C: 0x00000100,  # Transfer size
    }
    await tb.configure_system(config)

    # 2. Perform DMA transfer via AXI4
    src_addr = 0x10000000
    dst_addr = 0x20000000
    transfer_size = 64  # bytes

    dma_data = await tb.dma_transfer(src_addr, dst_addr, transfer_size)

    # 3. Stream data via AXIS4
    stream_data = [0x1000 + i for i in range(16)]
    received_stream = await tb.stream_data(stream_data)

    # 4. Verify results
    assert received_stream == stream_data, "Stream data mismatch"
    tb.log.info("Multi-protocol test PASSED")
```

### Concurrent Protocol Activity

```python
@cocotb.test()
async def test_concurrent_protocols(dut):
    """Test simultaneous activity on multiple protocols."""
    tb = SystemTB(dut)
    await tb.setup_clocks_and_reset()

    # Configure system first
    config = {0x0000: 0x1, 0x0004: 0x100}
    await tb.configure_system(config)

    # Launch concurrent tasks
    async def apb_config_updates():
        """Continuously update configuration."""
        for i in range(20):
            await tb.apb_config.write(0x0010 + (i * 4), 0xC0DE0000 + i)
            await tb.wait_clocks('aclk', 5)

    async def axi_memory_traffic():
        """Generate AXI memory traffic."""
        for i in range(10):
            addr = 0x80000000 + (i * 0x1000)
            data = [0xDATA0000 + j for j in range(8)]
            await tb.axi_write_burst(addr, data)
            await tb.wait_clocks('aclk', 10)

    async def axis_streaming():
        """Generate AXIS streaming traffic."""
        for batch in range(5):
            data = [0x5000 + (batch * 100) + i for i in range(10)]
            await tb.stream_data(data)
            await tb.wait_clocks('aclk', 20)

    # Run all protocols concurrently
    tasks = [
        cocotb.start_soon(apb_config_updates()),
        cocotb.start_soon(axi_memory_traffic()),
        cocotb.start_soon(axis_streaming())
    ]

    # Wait for all tasks to complete
    for task in tasks:
        await task

    tb.log.info("Concurrent protocol test PASSED")
```

## End-to-End Data Path Verification

System tests must verify complete data paths from input to output.

### End-to-End Test Pattern

```python
class DataPathTB(TBBase):
    """
    Testbench for end-to-end data path verification.

    Data flow: Input Stream → Processing → Memory → Output Stream
    """

    def __init__(self, dut):
        super().__init__(dut)
        self.clk_name = 'aclk'

        # Input/Output interfaces
        self.input_stream = AXIS4Master(dut, dut.aclk, "s_axis_", 32, self.log)
        self.output_stream = AXIS4Slave(dut, dut.aclk, "m_axis_", 32, self.log)

        # Memory interface
        self.memory_if = AXI4MasterWrite(dut, dut.aclk, "m_axi_", 32, 32, 4, log=self.log)

        # Data tracking
        self.input_data = []
        self.output_data = []
        self.memory_writes = []

    async def setup_clocks_and_reset(self):
        await self.start_clock(self.clk_name, freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks(self.clk_name, 10)
        await self.deassert_reset()

    async def assert_reset(self):
        self.dut.aresetn.value = 0

    async def deassert_reset(self):
        self.dut.aresetn.value = 1

    async def monitor_memory_writes(self):
        """Background task to monitor memory writes."""
        while True:
            # Wait for AXI write address
            if hasattr(self.dut, 'm_axi_awvalid'):
                if int(self.dut.m_axi_awvalid.value) == 1 and \
                   int(self.dut.m_axi_awready.value) == 1:
                    addr = int(self.dut.m_axi_awaddr.value)
                    self.memory_writes.append(addr)
                    self.log.debug(f"Memory write detected: addr=0x{addr:08X}")

            await self.wait_clocks(self.clk_name, 1)

    async def end_to_end_test(self, test_data, expected_transform=None):
        """
        Execute end-to-end data path test.

        Args:
            test_data: Input data list
            expected_transform: Function to compute expected output (optional)

        Returns:
            Success status and verification results
        """
        self.log.info(f"End-to-end test: {len(test_data)} samples")

        # Start monitoring
        monitor_task = cocotb.start_soon(self.monitor_memory_writes())

        # Send input data
        self.input_data = test_data
        for i, data in enumerate(test_data):
            packet = {
                'tdata': data,
                'tkeep': 0xF,
                'tlast': 1 if i == len(test_data) - 1 else 0,
                'tuser': 0
            }
            await self.input_stream.send(packet)

        # Collect output data
        self.output_data = []
        for i in range(len(test_data)):
            packet = await self.output_stream.recv()
            self.output_data.append(packet['tdata'])

        # Stop monitoring
        monitor_task.kill()

        # Verify data integrity
        if expected_transform:
            expected_output = [expected_transform(x) for x in test_data]
            assert self.output_data == expected_output, \
                f"Output mismatch: expected={expected_output}, got={self.output_data}"

        # Verify memory activity
        self.log.info(f"Memory writes: {len(self.memory_writes)}")

        return {
            'success': True,
            'input_count': len(self.input_data),
            'output_count': len(self.output_data),
            'memory_writes': len(self.memory_writes),
            'data_match': self.input_data == self.output_data if not expected_transform else True
        }


@cocotb.test()
async def test_data_path_passthrough(dut):
    """Test data path with passthrough processing."""
    tb = DataPathTB(dut)
    await tb.setup_clocks_and_reset()

    # Test with passthrough (no transformation)
    test_data = [0x100 + i for i in range(32)]

    results = await tb.end_to_end_test(test_data)

    assert results['success'], "End-to-end test failed"
    assert results['input_count'] == results['output_count'], "Data count mismatch"
    assert results['data_match'], "Data integrity check failed"

    tb.log.info("Data path passthrough test PASSED")


@cocotb.test()
async def test_data_path_transformation(dut):
    """Test data path with data transformation."""
    tb = DataPathTB(dut)
    await tb.setup_clocks_and_reset()

    # Test with transformation (e.g., data + 0x1000)
    test_data = [0x100 + i for i in range(32)]
    transform_fn = lambda x: (x + 0x1000) & 0xFFFFFFFF

    results = await tb.end_to_end_test(test_data, expected_transform=transform_fn)

    assert results['success'], "End-to-end transformation test failed"
    tb.log.info("Data path transformation test PASSED")
```

### Data Integrity Verification

```python
import hashlib

class DataIntegrityChecker:
    """Verify data integrity through system."""

    def __init__(self, log):
        self.log = log
        self.input_checksums = {}
        self.output_checksums = {}

    def compute_checksum(self, data_list):
        """Compute checksum for data verification."""
        data_bytes = b''.join(x.to_bytes(4, 'little') for x in data_list)
        return hashlib.sha256(data_bytes).hexdigest()

    def record_input(self, transaction_id, data):
        """Record input data checksum."""
        checksum = self.compute_checksum(data)
        self.input_checksums[transaction_id] = checksum
        self.log.debug(f"Input[{transaction_id}]: {checksum[:16]}...")

    def verify_output(self, transaction_id, data):
        """Verify output data matches input."""
        output_checksum = self.compute_checksum(data)
        input_checksum = self.input_checksums.get(transaction_id)

        if input_checksum == output_checksum:
            self.log.info(f"Transaction {transaction_id}: Data integrity PASSED")
            return True
        else:
            self.log.error(f"Transaction {transaction_id}: Data integrity FAILED")
            self.log.error(f"  Expected: {input_checksum[:16]}...")
            self.log.error(f"  Got:      {output_checksum[:16]}...")
            return False


@cocotb.test()
async def test_data_integrity(dut):
    """Verify data integrity through complete system."""
    tb = DataPathTB(dut)
    await tb.setup_clocks_and_reset()

    integrity_checker = DataIntegrityChecker(tb.log)

    # Test multiple transactions
    for tid in range(10):
        # Generate test data
        test_data = [0x10000 * tid + i for i in range(16)]

        # Record input checksum
        integrity_checker.record_input(tid, test_data)

        # Send through system
        results = await tb.end_to_end_test(test_data)

        # Verify output checksum
        assert integrity_checker.verify_output(tid, tb.output_data), \
            f"Data integrity check failed for transaction {tid}"

    tb.log.info("Data integrity test PASSED: All transactions verified")
```

## System-Level Scoreboards

System scoreboards verify correct behavior across multiple components and protocols.

### Multi-Protocol Scoreboard

```python
from collections import deque, defaultdict

class SystemScoreboard:
    """
    System-level scoreboard for multi-protocol verification.

    Tracks transactions across AXI, APB, and AXIS interfaces.
    """

    def __init__(self, log):
        self.log = log

        # Transaction queues by protocol
        self.axi_transactions = deque()
        self.apb_transactions = deque()
        self.axis_transactions = deque()

        # Expected vs actual tracking
        self.expected_outputs = deque()
        self.actual_outputs = deque()

        # Statistics
        self.stats = defaultdict(int)

    def record_axi_transaction(self, addr, data, operation):
        """Record AXI transaction."""
        transaction = {
            'protocol': 'axi4',
            'addr': addr,
            'data': data,
            'operation': operation,
            'timestamp': cocotb.utils.get_sim_time(units='ns')
        }
        self.axi_transactions.append(transaction)
        self.stats['axi_total'] += 1
        self.log.debug(f"AXI {operation}: addr=0x{addr:08X}")

    def record_apb_transaction(self, addr, data, operation):
        """Record APB transaction."""
        transaction = {
            'protocol': 'apb',
            'addr': addr,
            'data': data,
            'operation': operation,
            'timestamp': cocotb.utils.get_sim_time(units='ns')
        }
        self.apb_transactions.append(transaction)
        self.stats['apb_total'] += 1

    def record_axis_packet(self, data, last):
        """Record AXIS packet."""
        packet = {
            'protocol': 'axis4',
            'data': data,
            'last': last,
            'timestamp': cocotb.utils.get_sim_time(units='ns')
        }
        self.axis_transactions.append(packet)
        self.stats['axis_total'] += 1

    def expect_output(self, data):
        """Record expected output data."""
        self.expected_outputs.append(data)

    def check_output(self, data):
        """Verify output data against expected."""
        if not self.expected_outputs:
            self.log.error(f"Unexpected output: 0x{data:08X}")
            self.stats['errors'] += 1
            return False

        expected = self.expected_outputs.popleft()
        if data == expected:
            self.stats['matches'] += 1
            return True
        else:
            self.log.error(f"Output mismatch: expected=0x{expected:08X}, got=0x{data:08X}")
            self.stats['mismatches'] += 1
            return False

    def verify_transaction_ordering(self):
        """Verify transactions occurred in valid order."""
        # Get all transactions sorted by timestamp
        all_transactions = (
            list(self.axi_transactions) +
            list(self.apb_transactions) +
            list(self.axis_transactions)
        )
        all_transactions.sort(key=lambda x: x['timestamp'])

        # Verify ordering constraints
        last_config_time = 0
        errors = []

        for txn in all_transactions:
            if txn['protocol'] == 'apb':
                last_config_time = txn['timestamp']
            elif txn['protocol'] == 'axi4' and txn['operation'] == 'write':
                # AXI writes should occur after configuration
                if txn['timestamp'] < last_config_time + 100:  # 100ns minimum
                    errors.append(f"AXI write too soon after config: {txn['timestamp']}ns")

        if errors:
            for error in errors:
                self.log.error(error)
            return False

        self.log.info("Transaction ordering verification PASSED")
        return True

    def generate_report(self):
        """Generate comprehensive test report."""
        report = []
        report.append("\n" + "="*70)
        report.append("System Scoreboard Report")
        report.append("="*70)
        report.append(f"AXI Transactions:   {self.stats['axi_total']}")
        report.append(f"APB Transactions:   {self.stats['apb_total']}")
        report.append(f"AXIS Packets:       {self.stats['axis_total']}")
        report.append(f"Output Matches:     {self.stats['matches']}")
        report.append(f"Output Mismatches:  {self.stats['mismatches']}")
        report.append(f"Errors:             {self.stats['errors']}")

        success_rate = 0
        total_checks = self.stats['matches'] + self.stats['mismatches']
        if total_checks > 0:
            success_rate = (self.stats['matches'] / total_checks) * 100
        report.append(f"Success Rate:       {success_rate:.1f}%")
        report.append("="*70)

        return '\n'.join(report)


@cocotb.test()
async def test_with_system_scoreboard(dut):
    """Test with system-level scoreboard verification."""
    tb = SystemTB(dut)
    await tb.setup_clocks_and_reset()

    scoreboard = SystemScoreboard(tb.log)

    # Configure system (record in scoreboard)
    config = {0x0000: 0x1, 0x0004: 0x100}
    for addr, data in config.items():
        await tb.apb_config.write(addr, data)
        scoreboard.record_apb_transaction(addr, data, 'write')

    # Perform data transfers
    test_data = [0x1000 + i for i in range(16)]
    for data in test_data:
        scoreboard.expect_output(data)

    # Execute system operations
    addr = 0x80000000
    await tb.axi_write_burst(addr, test_data)
    scoreboard.record_axi_transaction(addr, test_data, 'write')

    # Stream data
    received = await tb.stream_data(test_data)

    # Verify outputs
    for data in received:
        scoreboard.check_output(data)

    # Verify transaction ordering
    assert scoreboard.verify_transaction_ordering(), "Transaction ordering violation"

    # Generate report
    report = scoreboard.generate_report()
    tb.log.info(report)

    # Check success criteria
    assert scoreboard.stats['mismatches'] == 0, "Output mismatches detected"
    assert scoreboard.stats['errors'] == 0, "Errors detected"

    tb.log.info("System scoreboard test PASSED")
```

## Test Scenarios and Use Cases

### Scenario 1: DMA Transfer with Configuration

```python
@cocotb.test()
async def test_dma_scenario(dut):
    """
    Realistic DMA transfer scenario:
    1. Configure DMA via APB
    2. Write source data to memory
    3. Trigger DMA transfer
    4. Verify destination data
    """
    tb = SystemTB(dut)
    await tb.setup_clocks_and_reset()

    # Step 1: Configure DMA controller
    dma_config = {
        0x0000: 0x00000001,  # DMA enable
        0x0004: 0x80000000,  # Source address
        0x0008: 0x90000000,  # Destination address
        0x000C: 0x00001000,  # Transfer size (4KB)
        0x0010: 0x00000003,  # Configuration (burst, cache, etc.)
    }
    await tb.configure_system(dma_config)

    # Step 2: Write source data
    src_addr = 0x80000000
    src_data = [0xDEADBEEF + i for i in range(256)]  # 1KB of data
    await tb.axi_write_burst(src_addr, src_data)

    # Step 3: Trigger DMA transfer (write to control register)
    await tb.apb_config.write(0x0014, 0x00000001)  # Start DMA

    # Step 4: Wait for completion (poll status register)
    timeout = 10000
    cycles = 0
    while cycles < timeout:
        status = await tb.apb_config.read(0x0018)  # Status register
        if status & 0x1:  # DMA complete bit
            break
        await tb.wait_clocks('aclk', 10)
        cycles += 10

    assert cycles < timeout, "DMA transfer timeout"

    # Step 5: Verify destination data
    dst_addr = 0x90000000
    dst_data = await tb.axi_read_burst(dst_addr, len(src_data) * 4)

    assert dst_data == src_data, "DMA data verification failed"

    tb.log.info("DMA scenario test PASSED")
```

### Scenario 2: Streaming with Flow Control

```python
@cocotb.test()
async def test_streaming_flow_control(dut):
    """
    Streaming scenario with flow control:
    1. Configure stream parameters
    2. Send data with backpressure
    3. Verify rate limiting
    4. Check data integrity
    """
    tb = SystemTB(dut)
    await tb.setup_clocks_and_reset()

    # Configure stream parameters
    stream_config = {
        0x0020: 0x00000064,  # Rate limit: 100 packets/sec
        0x0024: 0x00000001,  # Enable flow control
        0x0028: 0x00000010,  # FIFO threshold
    }
    await tb.configure_system(stream_config)

    # Enable backpressure on output
    tb.axis_output.set_backpressure_mode('random', probability=0.5)

    # Send stream with monitoring
    test_data = [0x2000 + i for i in range(100)]
    start_time = cocotb.utils.get_sim_time(units='ns')

    received = await tb.stream_data(test_data)

    end_time = cocotb.utils.get_sim_time(units='ns')
    duration_ns = end_time - start_time

    # Verify data integrity
    assert received == test_data, "Stream data mismatch"

    # Verify rate limiting
    expected_min_duration = len(test_data) * 10  # Minimum based on rate limit
    assert duration_ns >= expected_min_duration, \
        f"Transfer too fast: {duration_ns}ns < {expected_min_duration}ns"

    tb.log.info(f"Stream with flow control PASSED: {duration_ns}ns")
```

### Scenario 3: Error Injection and Recovery

```python
@cocotb.test()
async def test_error_recovery(dut):
    """
    Error recovery scenario:
    1. Normal operation
    2. Inject error condition
    3. Verify error detection
    4. Verify recovery
    5. Resume normal operation
    """
    tb = SystemTB(dut)
    await tb.setup_clocks_and_reset()

    # Phase 1: Normal operation
    tb.log.info("Phase 1: Normal operation")
    normal_data = [0x100 + i for i in range(10)]
    result1 = await tb.end_to_end_test(normal_data)
    assert result1['success'], "Normal operation failed"

    # Phase 2: Inject error (invalid address)
    tb.log.info("Phase 2: Error injection")
    error_addr = 0xBADADDR  # Invalid address
    error_detected = False

    try:
        await tb.axi_read_burst(error_addr, 16)
    except Exception as e:
        error_detected = True
        tb.log.info(f"Error detected as expected: {e}")

    assert error_detected, "Error not detected"

    # Phase 3: Verify error status
    error_status = await tb.apb_config.read(0x0030)  # Error status register
    assert error_status & 0x1, "Error status not set"

    # Phase 4: Clear error and recover
    await tb.apb_config.write(0x0030, 0x1)  # Clear error
    await tb.wait_clocks('aclk', 10)

    # Phase 5: Resume normal operation
    tb.log.info("Phase 5: Resume normal operation")
    normal_data2 = [0x200 + i for i in range(10)]
    result2 = await tb.end_to_end_test(normal_data2)
    assert result2['success'], "Recovery failed"

    tb.log.info("Error recovery scenario PASSED")
```

## Regression Test Organization

### Test Suite Structure

```python
"""
System regression test suite organization.

Test levels:
- smoke: Quick sanity checks (~30s)
- basic: Core functionality (~2min)
- extended: Comprehensive coverage (~10min)
- stress: Long-running stress tests (~30min)
- nightly: Full regression suite (~1hr)
"""

import pytest
import os

# Test level selection
test_level = os.environ.get('TEST_LEVEL', 'basic')

# Smoke tests (quick sanity)
smoke_tests = [
    'test_basic_reset',
    'test_simple_config',
    'test_single_transaction'
]

# Basic tests (core functionality)
basic_tests = smoke_tests + [
    'test_multi_protocol_operation',
    'test_dma_scenario',
    'test_streaming_flow_control'
]

# Extended tests (comprehensive)
extended_tests = basic_tests + [
    'test_concurrent_protocols',
    'test_data_path_transformation',
    'test_error_recovery',
    'test_transaction_ordering'
]

# Stress tests (long-running)
stress_tests = [
    'test_sustained_bandwidth',
    'test_maximum_outstanding',
    'test_random_stress',
    'test_corner_cases'
]

# Select tests based on level
if test_level == 'smoke':
    selected_tests = smoke_tests
elif test_level == 'basic':
    selected_tests = basic_tests
elif test_level == 'extended':
    selected_tests = extended_tests
elif test_level == 'stress':
    selected_tests = stress_tests
elif test_level == 'nightly':
    selected_tests = extended_tests + stress_tests
else:
    selected_tests = basic_tests

# Pytest parametrization
@pytest.mark.parametrize("test_name", selected_tests)
def test_system_regression(test_name):
    """Execute selected system tests."""
    # Test implementation...
    pass
```

### Regression Configuration

```json
{
    "regression_suites": {
        "smoke": {
            "timeout": "5min",
            "tests": ["test_basic_reset", "test_simple_config"],
            "run_on": "every_commit"
        },
        "nightly": {
            "timeout": "2hr",
            "tests": ["all"],
            "run_on": "nightly",
            "coverage": true
        },
        "weekly": {
            "timeout": "8hr",
            "tests": ["all"],
            "stress_tests": true,
            "performance_benchmarks": true,
            "run_on": "weekly"
        }
    },
    "coverage_goals": {
        "line_coverage": 95,
        "branch_coverage": 90,
        "functional_coverage": 85
    }
}
```

## Performance Characterization

### System Bandwidth Test

```python
@cocotb.test()
async def test_system_bandwidth(dut):
    """Characterize system bandwidth under various conditions."""
    tb = SystemTB(dut)
    await tb.setup_clocks_and_reset()

    test_scenarios = [
        {'name': 'Single Master', 'masters': 1, 'burst_size': 16},
        {'name': 'Dual Master', 'masters': 2, 'burst_size': 16},
        {'name': 'Quad Master', 'masters': 4, 'burst_size': 8},
        {'name': 'Max Outstanding', 'masters': 1, 'burst_size': 16, 'outstanding': 8},
    ]

    results = []

    for scenario in test_scenarios:
        tb.log.info(f"Testing: {scenario['name']}")

        start_time = cocotb.utils.get_sim_time(units='ns')

        # Execute test scenario
        # (Implementation depends on DUT architecture)

        end_time = cocotb.utils.get_sim_time(units='ns')
        duration = end_time - start_time

        # Calculate metrics
        bytes_transferred = 1024 * 1024  # 1MB
        bandwidth_mbps = (bytes_transferred * 1000) / duration

        results.append({
            'scenario': scenario['name'],
            'bandwidth': bandwidth_mbps,
            'duration': duration
        })

        tb.log.info(f"{scenario['name']}: {bandwidth_mbps:.2f} MB/s")

    # Generate report
    tb.log.info("\nBandwidth Characterization Results:")
    for result in results:
        tb.log.info(f"  {result['scenario']:20s}: {result['bandwidth']:8.2f} MB/s")
```

### System Latency Analysis

```python
@cocotb.test()
async def test_system_latency(dut):
    """Analyze end-to-end system latency."""
    tb = DataPathTB(dut)
    await tb.setup_clocks_and_reset()

    latency_measurements = []

    # Measure latency for various packet sizes
    packet_sizes = [1, 4, 16, 64, 256]

    for size in packet_sizes:
        test_data = list(range(size))
        latencies = []

        for trial in range(10):
            start = cocotb.utils.get_sim_time(units='ns')

            # Send input
            for data in test_data:
                packet = {'tdata': data, 'tkeep': 0xF, 'tlast': 0, 'tuser': 0}
                await tb.input_stream.send(packet)

            # Measure until first output
            first_output = await tb.output_stream.recv()

            end = cocotb.utils.get_sim_time(units='ns')
            latencies.append(end - start)

        # Calculate statistics
        avg_latency = sum(latencies) / len(latencies)
        min_latency = min(latencies)
        max_latency = max(latencies)

        latency_measurements.append({
            'size': size,
            'avg': avg_latency,
            'min': min_latency,
            'max': max_latency
        })

        tb.log.info(f"Size {size:3d}: Avg={avg_latency:.1f}ns, "
                   f"Min={min_latency:.1f}ns, Max={max_latency:.1f}ns")

    # Verify latency requirements
    for measurement in latency_measurements:
        assert measurement['max'] < 2000, \
            f"Latency too high for size {measurement['size']}"
```

## Debug and Analysis

### Transaction Logging

```python
class TransactionLogger:
    """Comprehensive transaction logging for debug analysis."""

    def __init__(self, log_file):
        self.log_file = log_file
        self.transactions = []

    def log_transaction(self, protocol, operation, details):
        """Log transaction with timestamp."""
        entry = {
            'timestamp': cocotb.utils.get_sim_time(units='ns'),
            'protocol': protocol,
            'operation': operation,
            'details': details
        }
        self.transactions.append(entry)

    def save_log(self):
        """Save transaction log to file."""
        import json
        with open(self.log_file, 'w') as f:
            json.dump(self.transactions, f, indent=2)

    def generate_timeline(self):
        """Generate timeline visualization data."""
        timeline = []
        for txn in self.transactions:
            timeline.append({
                'time': txn['timestamp'],
                'protocol': txn['protocol'],
                'event': f"{txn['operation']}: {txn['details']}"
            })
        return timeline
```

### Performance Profiling

```python
class PerformanceProfiler:
    """Profile system performance characteristics."""

    def __init__(self, log):
        self.log = log
        self.metrics = {
            'axi_transactions': 0,
            'apb_transactions': 0,
            'axis_packets': 0,
            'total_bytes': 0,
            'start_time': 0,
            'end_time': 0
        }

    def start_profiling(self):
        """Begin profiling session."""
        self.metrics['start_time'] = cocotb.utils.get_sim_time(units='ns')

    def stop_profiling(self):
        """End profiling session and generate report."""
        self.metrics['end_time'] = cocotb.utils.get_sim_time(units='ns')
        duration = self.metrics['end_time'] - self.metrics['start_time']

        # Calculate metrics
        bandwidth = (self.metrics['total_bytes'] * 1000) / duration  # MB/s
        axi_rate = (self.metrics['axi_transactions'] * 1e9) / duration  # txn/s
        apb_rate = (self.metrics['apb_transactions'] * 1e9) / duration  # txn/s

        self.log.info("\nPerformance Profile:")
        self.log.info(f"  Duration:         {duration:.0f} ns")
        self.log.info(f"  AXI Transactions: {self.metrics['axi_transactions']} ({axi_rate:.0f} txn/s)")
        self.log.info(f"  APB Transactions: {self.metrics['apb_transactions']} ({apb_rate:.0f} txn/s)")
        self.log.info(f"  AXIS Packets:     {self.metrics['axis_packets']}")
        self.log.info(f"  Bandwidth:        {bandwidth:.2f} MB/s")
```

## Best Practices

### 1. Layered Testing Strategy

```python
# Build tests in layers
# Layer 1: Unit tests (individual modules)
# Layer 2: Integration tests (subsystems)
# Layer 3: System tests (complete system)

# Good: Progressive complexity
def test_hierarchy():
    # Start simple
    test_basic_config()        # Unit level
    test_protocol_interface()  # Integration level
    test_end_to_end_system()  # System level
```

### 2. Realistic Traffic Patterns

```python
# Good: Use realistic access patterns
async def generate_realistic_traffic():
    # Mix of sequential and random access
    # Bursts interspersed with idle periods
    # Multiple concurrent streams
    pass

# Bad: Unrealistic uniform traffic
async def generate_uniform_traffic():
    # Continuous maximum bandwidth
    # No idle periods
    # Perfectly regular patterns
    pass
```

### 3. Comprehensive Verification

```python
# Good: Verify at multiple levels
- Protocol compliance
- Data integrity
- Performance metrics
- Error handling
- Recovery mechanisms

# Bad: Only check functional correctness
- Data matches
- (Missing timing, performance, errors)
```

### 4. Automated Regression

```python
# Good: Organized test suites
regression_config = {
    'smoke': ['quick_sanity'],
    'nightly': ['comprehensive'],
    'weekly': ['stress', 'performance']
}

# Bad: Ad-hoc test execution
# "Run tests manually when you remember"
```

## Anti-Patterns to Avoid

### Don't Test in Isolation

```python
# ❌ Wrong: Test protocols separately
test_axi_only()
test_apb_only()
test_axis_only()

# ✅ Correct: Test protocols together
test_concurrent_protocols()
test_protocol_interactions()
```

### Don't Ignore Performance

```python
# ❌ Wrong: Only check functionality
assert data_correct  # Is it right?

# ✅ Correct: Check performance too
assert data_correct      # Is it right?
assert bandwidth > 100   # Is it fast enough?
assert latency < 1000    # Is it responsive?
```

### Don't Skip Error Cases

```python
# ❌ Wrong: Only test happy path
test_normal_operation()

# ✅ Correct: Test error scenarios
test_normal_operation()
test_error_injection()
test_error_recovery()
test_corner_cases()
```

### Don't Use Magic Numbers

```python
# ❌ Wrong: Unexplained constants
await Timer(100, units='ns')  # Why 100?

# ✅ Correct: Named constants
RESET_DURATION_NS = 100
await Timer(RESET_DURATION_NS, units='ns')
```

## Summary

This guide covered system-level testing strategies:

1. **Multi-Protocol Integration** - Testing AXI4, APB, AXIS4 together
2. **End-to-End Verification** - Complete data path validation
3. **System Scoreboards** - Multi-component verification
4. **Test Scenarios** - Realistic use cases and workflows
5. **Regression Organization** - Structured test suites
6. **Performance Characterization** - Bandwidth and latency analysis
7. **Debug and Analysis** - Transaction logging and profiling

Key principles:
- Test realistic scenarios, not isolated cases
- Verify protocols interact correctly
- Measure system-level performance
- Use comprehensive scoreboards
- Organize regression suites by complexity
- Include error injection and recovery
- Profile and analyze system behavior

---

[Back to Test Tutorial Index](index.md)

---
