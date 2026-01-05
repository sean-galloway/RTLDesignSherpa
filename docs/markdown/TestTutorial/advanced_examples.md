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

# Advanced CocoTB Testing Examples

Comprehensive examples of advanced testing techniques using CocoTB for complex RTL verification scenarios, including protocol compliance, performance analysis, and system-level testing.

## Complex Protocol Testing

### AXI4 Master Testing

```python
import cocotb
from cocotb.triggers import RisingEdge, FallingEdge, Timer
from cocotb.clock import Clock
import random
from collections import deque

class AXI4MasterTB:
    def __init__(self, dut):
        self.dut = dut
        self.clock = Clock(dut.aclk, 10, units="ns")
        cocotb.start_soon(self.clock.start())

        # Outstanding transaction tracking
        self.outstanding_reads = deque()
        self.outstanding_writes = deque()

        # Performance metrics
        self.total_transactions = 0
        self.successful_transactions = 0

    async def reset_sequence(self):
        """Perform proper AXI reset sequence"""
        self.dut.aresetn.value = 0

        # Initialize all input signals
        self.dut.awready.value = 0
        self.dut.wready.value = 0
        self.dut.bvalid.value = 0
        self.dut.arready.value = 0
        self.dut.rvalid.value = 0

        await Timer(100, units='ns')
        self.dut.aresetn.value = 1
        await Timer(50, units='ns')

    async def write_transaction(self, addr, data, length=0, size=2):
        """Execute AXI4 write transaction with full protocol compliance"""
        # Address phase
        self.dut.awaddr.value = addr
        self.dut.awlen.value = length
        self.dut.awsize.value = size
        self.dut.awburst.value = 1  # INCR
        self.dut.awvalid.value = 1

        # Wait for address acceptance
        await RisingEdge(self.dut.aclk)
        while not (self.dut.awvalid.value and self.dut.awready.value):
            await RisingEdge(self.dut.aclk)

        self.dut.awvalid.value = 0

        # Data phase
        for i in range(length + 1):
            self.dut.wdata.value = data[i] if isinstance(data, list) else data
            self.dut.wstrb.value = 0xF  # All bytes valid
            self.dut.wlast.value = 1 if i == length else 0
            self.dut.wvalid.value = 1

            await RisingEdge(self.dut.aclk)
            while not (self.dut.wvalid.value and self.dut.wready.value):
                await RisingEdge(self.dut.aclk)

        self.dut.wvalid.value = 0

        # Wait for write response
        await self.wait_write_response()

        self.total_transactions += 1

    async def read_transaction(self, addr, length=0, size=2):
        """Execute AXI4 read transaction"""
        self.dut.araddr.value = addr
        self.dut.arlen.value = length
        self.dut.arsize.value = size
        self.dut.arburst.value = 1  # INCR
        self.dut.arvalid.value = 1

        # Wait for address acceptance
        await RisingEdge(self.dut.aclk)
        while not (self.dut.arvalid.value and self.dut.arready.value):
            await RisingEdge(self.dut.aclk)

        self.dut.arvalid.value = 0

        # Wait for read data
        read_data = await self.wait_read_data(length + 1)

        self.total_transactions += 1
        return read_data

    async def wait_write_response(self):
        """Wait for write response with timeout"""
        self.dut.bready.value = 1
        timeout = 0

        while not (self.dut.bvalid.value and self.dut.bready.value):
            await RisingEdge(self.dut.aclk)
            timeout += 1
            if timeout > 1000:
                raise TimeoutError("Write response timeout")

        response = self.dut.bresp.value
        self.dut.bready.value = 0

        if response == 0:  # OKAY
            self.successful_transactions += 1

        return response

    async def wait_read_data(self, beats):
        """Wait for read data with timeout"""
        self.dut.rready.value = 1
        read_data = []
        received_beats = 0
        timeout = 0

        while received_beats < beats:
            if self.dut.rvalid.value and self.dut.rready.value:
                read_data.append(int(self.dut.rdata.value))
                received_beats += 1

                if self.dut.rresp.value != 0:  # Not OKAY
                    raise Exception(f"Read error response: {self.dut.rresp.value}")

                if self.dut.rlast.value and received_beats != beats:
                    raise Exception("Unexpected RLAST assertion")

            await RisingEdge(self.dut.aclk)
            timeout += 1
            if timeout > 1000:
                raise TimeoutError("Read data timeout")

        self.dut.rready.value = 0
        self.successful_transactions += 1
        return read_data

@cocotb.test()
async def test_axi4_burst_operations(dut):
    """Test various AXI4 burst operations"""
    tb = AXI4MasterTB(dut)
    await tb.reset_sequence()

    # Test different burst lengths
    for burst_len in [0, 1, 3, 7, 15]:  # 1, 2, 4, 8, 16 beats
        addr = 0x1000 + (burst_len * 0x100)
        test_data = [0xDEADBEEF + i for i in range(burst_len + 1)]

        # Write burst
        await tb.write_transaction(addr, test_data, length=burst_len)

        # Read back and verify
        read_data = await tb.read_transaction(addr, length=burst_len)
        assert read_data == test_data, f"Burst length {burst_len}: Data mismatch"

    # Performance check
    success_rate = tb.successful_transactions / tb.total_transactions
    assert success_rate > 0.95, f"Success rate too low: {success_rate:.2%}"
```

### Memory Controller Verification

```python
class MemoryModel:
    """Behavioral memory model for verification"""
    def __init__(self, size_mb=64):
        self.size = size_mb * 1024 * 1024
        self.memory = {}
        self.access_log = []

    def write(self, addr, data, strb=0xF):
        """Write data with byte strobes"""
        if addr >= self.size:
            raise ValueError(f"Address {addr:08x} out of range")

        if addr not in self.memory:
            self.memory[addr] = 0

        # Apply byte strobes
        for i in range(4):
            if strb & (1 << i):
                byte_val = (data >> (i * 8)) & 0xFF
                self.memory[addr] = (self.memory[addr] & ~(0xFF << (i * 8))) | (byte_val << (i * 8))

        self.access_log.append(('W', addr, data, strb))

    def read(self, addr):
        """Read data from memory"""
        if addr >= self.size:
            raise ValueError(f"Address {addr:08x} out of range")

        data = self.memory.get(addr, 0)
        self.access_log.append(('R', addr, data, 0xF))
        return data

class MemoryControllerTB:
    def __init__(self, dut):
        self.dut = dut
        self.memory = MemoryModel(64)  # 64MB memory
        self.clock = Clock(dut.clk, 10, units="ns")
        cocotb.start_soon(self.clock.start())
        cocotb.start_soon(self.memory_interface_driver())

    async def memory_interface_driver(self):
        """Drive memory interface responses"""
        while True:
            # Simulate memory latency
            if self.dut.mem_req.value:
                await Timer(random.randint(5, 15), units='ns')  # Variable latency

                addr = int(self.dut.mem_addr.value)
                if self.dut.mem_write.value:
                    data = int(self.dut.mem_wdata.value)
                    strb = int(self.dut.mem_strb.value)
                    self.memory.write(addr, data, strb)
                else:
                    data = self.memory.read(addr)
                    self.dut.mem_rdata.value = data

                self.dut.mem_ack.value = 1
                await RisingEdge(self.dut.clk)
                self.dut.mem_ack.value = 0

            await RisingEdge(self.dut.clk)

@cocotb.test()
async def test_memory_controller_performance(dut):
    """Test memory controller under various load conditions"""
    tb = MemoryControllerTB(dut)

    # Reset sequence
    dut.rst_n.value = 0
    await Timer(100, units='ns')
    dut.rst_n.value = 1
    await Timer(50, units='ns')

    # Performance test scenarios
    test_scenarios = [
        {"name": "Sequential Access", "pattern": "sequential"},
        {"name": "Random Access", "pattern": "random"},
        {"name": "Stride Access", "pattern": "stride"},
        {"name": "Mixed Read/Write", "pattern": "mixed"}
    ]

    for scenario in test_scenarios:
        start_time = cocotb.utils.get_sim_time(units='ns')

        if scenario["pattern"] == "sequential":
            await run_sequential_access_test(dut, tb)
        elif scenario["pattern"] == "random":
            await run_random_access_test(dut, tb)
        elif scenario["pattern"] == "stride":
            await run_stride_access_test(dut, tb)
        elif scenario["pattern"] == "mixed":
            await run_mixed_access_test(dut, tb)

        end_time = cocotb.utils.get_sim_time(units='ns')
        duration = end_time - start_time

        print(f"{scenario['name']}: {duration}ns, "
              f"Throughput: {len(tb.memory.access_log)*4/(duration*1e-9):.2f} MB/s")
```

## System-Level Integration Testing

### Multi-Master Bus Testing

```python
class BusSystemTB:
    """Testbench for multi-master bus system"""
    def __init__(self, dut):
        self.dut = dut
        self.masters = []
        self.slaves = []
        self.transaction_log = []

        # Initialize multiple masters
        for i in range(4):  # 4 masters
            master = AXI4MasterTB(getattr(dut, f'm{i}_axi'))
            self.masters.append(master)

        # Initialize slaves (memory models)
        for i in range(2):  # 2 slaves
            slave = MemoryModel(32)
            self.slaves.append(slave)

    async def concurrent_master_test(self):
        """Test concurrent transactions from multiple masters"""
        # Start concurrent transactions
        tasks = []

        for i, master in enumerate(self.masters):
            # Each master accesses different address ranges
            base_addr = 0x10000000 + (i * 0x1000000)
            task = cocotb.start_soon(self.master_workload(master, base_addr, i))
            tasks.append(task)

        # Wait for all masters to complete
        await cocotb.utils.First(*tasks)

    async def master_workload(self, master, base_addr, master_id):
        """Individual master workload"""
        for transaction in range(100):
            addr = base_addr + (transaction * 16)
            data = 0xCAFE0000 + (master_id << 8) + transaction

            try:
                await master.write_transaction(addr, data)
                read_data = await master.read_transaction(addr)

                self.transaction_log.append({
                    'master': master_id,
                    'transaction': transaction,
                    'addr': addr,
                    'write_data': data,
                    'read_data': read_data[0],
                    'success': read_data[0] == data
                })

            except Exception as e:
                print(f"Master {master_id} transaction {transaction} failed: {e}")

@cocotb.test()
async def test_bus_arbitration_fairness(dut):
    """Test bus arbitration fairness under load"""
    tb = BusSystemTB(dut)

    # Reset all components
    dut.aresetn.value = 0
    await Timer(100, units='ns')
    dut.aresetn.value = 1
    await Timer(50, units='ns')

    # Run concurrent test
    await tb.concurrent_master_test()

    # Analyze fairness
    master_transactions = {}
    for log_entry in tb.transaction_log:
        master_id = log_entry['master']
        master_transactions[master_id] = master_transactions.get(master_id, 0) + 1

    # Check fairness (no master should get more than 2x others)
    min_transactions = min(master_transactions.values())
    max_transactions = max(master_transactions.values())
    fairness_ratio = max_transactions / min_transactions

    assert fairness_ratio < 2.0, f"Unfair arbitration: ratio={fairness_ratio:.2f}"

    # Check success rate
    successful = sum(1 for log in tb.transaction_log if log['success'])
    success_rate = successful / len(tb.transaction_log)
    assert success_rate > 0.99, f"Too many failed transactions: {success_rate:.2%}"
```

## Advanced Stimulus Generation

### Constrained Random Testing

```python
import random
from dataclasses import dataclass, field
from typing import List, Optional

@dataclass
class TransactionConstraints:
    """Constraints for random transaction generation"""
    min_addr: int = 0x00000000
    max_addr: int = 0xFFFFFFFF
    addr_alignment: int = 4

    min_size: int = 0  # 1 byte
    max_size: int = 3  # 8 bytes

    min_len: int = 0   # 1 beat
    max_len: int = 15  # 16 beats

    burst_types: List[int] = field(default_factory=lambda: [1, 2])  # INCR, WRAP

    # Weighted probabilities
    read_weight: float = 0.5
    write_weight: float = 0.5

    # Address patterns
    sequential_weight: float = 0.3
    random_weight: float = 0.4
    stride_weight: float = 0.3

class ConstrainedRandomGenerator:
    def __init__(self, constraints: TransactionConstraints, seed: Optional[int] = None):
        self.constraints = constraints
        self.rng = random.Random(seed)
        self.last_addr = constraints.min_addr

    def generate_transaction(self):
        """Generate a constrained random transaction"""
        # Determine operation type
        is_write = self.rng.random() < self.constraints.write_weight

        # Generate address based on pattern weights
        addr = self._generate_address()

        # Generate transaction parameters
        size = self.rng.randint(self.constraints.min_size, self.constraints.max_size)
        length = self.rng.randint(self.constraints.min_len, self.constraints.max_len)
        burst = self.rng.choice(self.constraints.burst_types)

        # Generate data for write transactions
        data = None
        if is_write:
            data = [self.rng.randint(0, 0xFFFFFFFF) for _ in range(length + 1)]

        return {
            'type': 'write' if is_write else 'read',
            'addr': addr,
            'size': size,
            'length': length,
            'burst': burst,
            'data': data
        }

    def _generate_address(self):
        """Generate address based on pattern weights"""
        pattern_choice = self.rng.choices(
            ['sequential', 'random', 'stride'],
            weights=[
                self.constraints.sequential_weight,
                self.constraints.random_weight,
                self.constraints.stride_weight
            ]
        )[0]

        if pattern_choice == 'sequential':
            addr = self.last_addr + self.constraints.addr_alignment
        elif pattern_choice == 'stride':
            stride = self.rng.choice([64, 256, 1024, 4096])  # Common cache line sizes
            addr = self.last_addr + stride
        else:  # random
            addr = self.rng.randint(
                self.constraints.min_addr,
                self.constraints.max_addr
            )

        # Ensure alignment
        addr = addr & ~(self.constraints.addr_alignment - 1)

        # Ensure within bounds
        addr = max(self.constraints.min_addr,
                  min(self.constraints.max_addr, addr))

        self.last_addr = addr
        return addr

@cocotb.test()
async def test_constrained_random_stimulus(dut):
    """Test with constrained random stimulus"""
    tb = AXI4MasterTB(dut)
    await tb.reset_sequence()

    # Setup constraints for realistic traffic
    constraints = TransactionConstraints(
        min_addr=0x80000000,
        max_addr=0x8FFFFFFF,
        addr_alignment=64,  # Cache line aligned
        read_weight=0.7,    # More reads than writes
        sequential_weight=0.5  # Favor sequential access
    )

    generator = ConstrainedRandomGenerator(constraints, seed=12345)

    # Generate and execute random transactions
    for i in range(1000):
        transaction = generator.generate_transaction()

        try:
            if transaction['type'] == 'write':
                await tb.write_transaction(
                    transaction['addr'],
                    transaction['data'],
                    transaction['length'],
                    transaction['size']
                )
            else:
                read_data = await tb.read_transaction(
                    transaction['addr'],
                    transaction['length'],
                    transaction['size']
                )

        except Exception as e:
            print(f"Transaction {i} failed: {e}")
            print(f"Transaction details: {transaction}")
            raise

    # Verify performance metrics
    assert tb.successful_transactions > 950, "Too many failed transactions"
```

## Performance and Stress Testing

### Bandwidth Testing

```python
@cocotb.test()
async def test_maximum_bandwidth(dut):
    """Test maximum sustainable bandwidth"""
    tb = AXI4MasterTB(dut)
    await tb.reset_sequence()

    # Configure for maximum bandwidth
    # - Large bursts (16 beats)
    # - Wide data (full width)
    # - No delays between transactions

    burst_size = 15  # 16 beats
    data_width_bytes = 4  # 32-bit data
    num_transactions = 100

    start_time = cocotb.utils.get_sim_time(units='ns')

    for i in range(num_transactions):
        addr = 0x80000000 + (i * 64)  # 64-byte aligned
        data = [0xDEADBEEF + j for j in range(16)]

        await tb.write_transaction(addr, data, length=burst_size)

    end_time = cocotb.utils.get_sim_time(units='ns')

    # Calculate achieved bandwidth
    total_bytes = num_transactions * 16 * data_width_bytes
    duration_ns = end_time - start_time
    bandwidth_mbps = (total_bytes * 1000) / duration_ns  # MB/s

    print(f"Achieved bandwidth: {bandwidth_mbps:.2f} MB/s")

    # Check against expected performance
    clock_freq_mhz = 100  # 100 MHz
    theoretical_max = clock_freq_mhz * data_width_bytes  # MB/s
    efficiency = bandwidth_mbps / theoretical_max

    assert efficiency > 0.8, f"Bandwidth efficiency too low: {efficiency:.2%}"

@cocotb.test()
async def test_latency_measurements(dut):
    """Measure transaction latency under various conditions"""
    tb = AXI4MasterTB(dut)
    await tb.reset_sequence()

    latency_measurements = []

    # Test different scenarios
    scenarios = [
        {"name": "Single Beat", "length": 0, "load": "light"},
        {"name": "4 Beat Burst", "length": 3, "load": "light"},
        {"name": "16 Beat Burst", "length": 15, "load": "light"},
        {"name": "Single Beat - Heavy Load", "length": 0, "load": "heavy"},
        {"name": "16 Beat Burst - Heavy Load", "length": 15, "load": "heavy"}
    ]

    for scenario in scenarios:
        # Start background load if needed
        if scenario["load"] == "heavy":
            # Start background traffic task
            background_task = cocotb.start_soon(generate_background_traffic(tb))

        latencies = []

        # Measure latency for multiple transactions
        for i in range(20):
            start = cocotb.utils.get_sim_time(units='ns')

            addr = 0x90000000 + (i * 64)
            await tb.write_transaction(addr, 0xTESTDATA, length=scenario["length"])

            end = cocotb.utils.get_sim_time(units='ns')
            latencies.append(end - start)

        if scenario["load"] == "heavy":
            background_task.kill()

        # Calculate statistics
        avg_latency = sum(latencies) / len(latencies)
        max_latency = max(latencies)
        min_latency = min(latencies)

        latency_measurements.append({
            'scenario': scenario["name"],
            'avg_ns': avg_latency,
            'min_ns': min_latency,
            'max_ns': max_latency
        })

        print(f"{scenario['name']}: Avg={avg_latency:.1f}ns, "
              f"Min={min_latency:.1f}ns, Max={max_latency:.1f}ns")

    # Verify latency requirements
    for measurement in latency_measurements:
        assert measurement['max_ns'] < 1000, \
            f"Latency too high for {measurement['scenario']}: {measurement['max_ns']:.1f}ns"

async def generate_background_traffic(tb):
    """Generate background traffic for stress testing"""
    while True:
        addr = random.randint(0x70000000, 0x7FFFFFFF) & 0xFFFFFFC0  # 64-byte aligned
        try:
            await tb.write_transaction(addr, random.randint(0, 0xFFFFFFFF))
            await Timer(random.randint(10, 50), units='ns')
        except:
            pass  # Ignore background failures
```

These advanced examples demonstrate sophisticated testing techniques that can be applied to complex RTL designs, providing comprehensive verification coverage and performance analysis.

---

[Back to Test Tutorial Index](index.md)

---