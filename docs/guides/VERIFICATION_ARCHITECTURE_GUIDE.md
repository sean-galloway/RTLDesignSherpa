# Verification Architecture Guide

**Version:** 1.0
**Date:** 2025-10-14
**Purpose:** Standard verification architecture for all RTL Design Sherpa subsystems

---

## Overview

This guide defines the mandatory three-layer verification architecture used across all subsystems (Common, AMBA, RAPIDS, etc.). Following this pattern ensures:
- **Reusability**: Same testbench used in unit, integration, and system tests
- **Maintainability**: Fix once, all tests benefit
- **Clarity**: Clear separation of infrastructure, intelligence, and verification
- **Scalability**: Easy to extend for complex scenarios

---

## Three-Layer Architecture

### Layer 1: Testbench Class (TB)

**Location:** `bin/CocoTBFramework/tbclasses/{subsystem}/{module}_tb.py`

**Purpose:** Reusable infrastructure and base methods

**Responsibilities:**
- BFM instantiation and management
- Clock and reset control
- DUT interface wrappers
- Base test methods (e.g., `run_basic_test()`, `run_stress_test()`)
- Protocol-specific utilities
- **NOT responsible for verification logic** (that's the scoreboard's job)

**Example:**
```python
# bin/CocoTBFramework/tbclasses/rapids/scheduler_tb.py
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

class SchedulerTB(TBBase):
    """Reusable testbench for RAPIDS Scheduler"""

    def __init__(self, dut):
        super().__init__(dut)
        # BFM instantiation
        self.apb_driver = APBDriver(dut, ...)
        self.axi_slave = AXI4SlaveWrite(dut, ...)

        # Scoreboard instantiation
        self.scoreboard = SchedulerScoreboard(
            aw_monitor=self.aw_monitor,
            w_monitor=self.w_monitor
        )

    async def setup_clocks_and_reset(self):
        """Standard initialization"""
        await self.start_clock('clk', freq=10, units='ns')
        await self.assert_reset()
        await self.wait_clocks('clk', 10)
        await self.deassert_reset()

    async def run_basic_test(self, num_ops=10):
        """Base method - reusable across tests"""
        for i in range(num_ops):
            await self.send_request(addr, data)
            # Scoreboard verifies in background

        # Final verification
        result = self.scoreboard.verify_all()
        self.scoreboard.clear_queues()
        return result
```

### Layer 2: Test Runner

**Location:** `val/{subsystem}/test_{module}.py`

**Purpose:** Test intelligence and scenario logic

**Responsibilities:**
- CocoTB test functions (prefixed with `cocotb_`)
- Pytest wrappers with parametrization
- Test-specific scenario logic
- **Imports** TB class (does NOT define it)
- Calls TB methods to execute tests

**Example:**
```python
# val/rapids/fub_tests/scheduler/test_scheduler.py
from CocoTBFramework.tbclasses.rapids.scheduler_tb import SchedulerTB

@cocotb.test()
async def cocotb_test_basic_flow(dut):
    """Test runner - uses TB methods"""
    tb = SchedulerTB(dut)  # Import from tbclasses/
    await tb.setup_clocks_and_reset()
    result = await tb.run_basic_test(num_ops=10)
    assert result, "Basic test failed"

@pytest.mark.parametrize("num_ops", [10, 50, 100])
def test_basic_flow(num_ops, ...):
    """Pytest wrapper - handles parameters"""
    run(verilog_sources=..., module=module, testcase="cocotb_test_basic_flow", ...)
```

### Layer 3: Scoreboard

**Location:** `bin/CocoTBFramework/scoreboards/{subsystem}/{module}_scoreboard.py`

**Purpose:** Transaction verification and checking

**Responsibilities:**
- Expected vs actual comparison
- Transaction checking using appropriate method:
  - **Queue access** for simple scenarios
  - **Memory models** for complex scenarios
- Coverage collection
- Error reporting
- Queue/state management

**Example:**
```python
# bin/CocoTBFramework/scoreboards/rapids/program_engine_scoreboard.py
class ProgramEngineScoreboard:
    """Scoreboard for program engine verification

    Uses direct queue access since program engine is:
    - Single-master
    - In-order writes
    - No address overlap
    """

    def __init__(self, aw_monitor, w_monitor):
        self.aw_monitor = aw_monitor
        self.w_monitor = w_monitor
        self.expected_transactions = []
        self.errors = []

    def expect_write(self, addr, data):
        """Record expected write transaction"""
        self.expected_transactions.append({'addr': addr, 'data': data})

    def check_transaction(self):
        """Verify write using direct queue access"""
        if not self.expected_transactions:
            return True

        expected = self.expected_transactions.pop(0)

        if self.aw_monitor._recvQ:
            aw_pkt = self.aw_monitor._recvQ.popleft()
            w_pkt = self.w_monitor._recvQ.popleft()

            if aw_pkt.addr != expected['addr']:
                self.errors.append(f"Address mismatch: expected 0x{expected['addr']:X}, got 0x{aw_pkt.addr:X}")
                return False

            if w_pkt.data != expected['data']:
                self.errors.append(f"Data mismatch: expected 0x{expected['data']:X}, got 0x{w_pkt.data:X}")
                return False

            return True

        self.errors.append("No transaction in queue")
        return False

    def verify_all(self):
        """Verify all expected transactions"""
        while self.expected_transactions:
            if not self.check_transaction():
                return False
        return True

    def clear_queues(self):
        """Clear queues after verification section"""
        self.aw_monitor._recvQ.clear()
        self.w_monitor._recvQ.clear()
        self.expected_transactions.clear()
        self.errors.clear()
```

---

## Verification Strategy: Queue Access vs Memory Models

### When to Use Each Approach

#### Direct Queue Access (Simple Scenarios)

**Use for:**
- Control paths (APB, configuration registers)
- Single-master systems
- In-order transactions
- No address overlap
- Simple point-to-point verification

**Pattern:**
```python
# Get transaction from monitor queue
aw_pkt = self.aw_monitor._recvQ.popleft()
w_pkt = self.w_monitor._recvQ.popleft()

# Verify
assert aw_pkt.addr == expected_addr
assert w_pkt.data == expected_data

# Clear after verification
self.aw_monitor._recvQ.clear()
self.w_monitor._recvQ.clear()
```

**Benefits:**
- Simple and direct
- Minimal overhead
- Easy to debug (inspect queue)
- No state management needed

**Examples:**
- ✅ Program engine writes (single-master, in-order)
- ✅ APB configuration registers (simple read/write)
- ✅ Descriptor interfaces (point-to-point)
- ✅ Control/status register access

#### Memory Models (Complex Scenarios)

**Use for:**
- Data paths (DMA, streaming data)
- Multi-master systems
- Out-of-order transactions
- Overlapping address ranges
- Need to track actual memory state
- Data integrity validation across transfers

**Pattern:**
```python
# Scoreboard with memory model
class DataPathScoreboard:
    def __init__(self, aw_monitor, w_monitor):
        self.aw_monitor = aw_monitor
        self.w_monitor = w_monitor
        self.memory_model = MemoryModel(size=0x100000)

    def process_write(self):
        """Process write transaction and update memory"""
        if self.aw_monitor._recvQ:
            aw_pkt = self.aw_monitor._recvQ.popleft()
            w_pkt = self.w_monitor._recvQ.popleft()

            # Update memory model
            self.memory_model.write(aw_pkt.addr, w_pkt.data)

    def verify_data(self, addr, expected_data):
        """Verify data at address"""
        actual_data = self.memory_model.read(addr)
        assert actual_data == expected_data
```

**Benefits:**
- Tracks memory state
- Handles address overlaps
- Supports out-of-order completion
- Validates data integrity
- Realistic memory behavior

**Examples:**
- ✅ DMA sink data path (burst writes, streaming)
- ✅ DMA source data path (burst reads)
- ✅ Multi-master AXI interconnect
- ✅ Cache coherency verification
- ✅ Memory subsystem testing

### Decision Tree

```
Need to verify transactions?
│
├─ Is it a control/config path (APB, simple writes)?
│  └─ YES → Use direct queue access
│
├─ Is it single-master, in-order, no address overlap?
│  └─ YES → Use direct queue access
│
├─ Is it a data path with bulk transfers?
│  └─ YES → Use memory model
│
├─ Multiple masters with overlapping addresses?
│  └─ YES → Use memory model
│
└─ Out-of-order transactions?
   └─ YES → Use memory model
```

### Comparison Table

| Characteristic | Queue Access | Memory Model |
|----------------|--------------|--------------|
| **Complexity** | Simple | Moderate |
| **Use Case** | Control paths | Data paths |
| **Masters** | Single | Single or multi |
| **Transaction Order** | In-order | Any order |
| **Address Overlap** | No | Yes |
| **State Tracking** | No | Yes |
| **Overhead** | Minimal | Moderate |
| **Setup Effort** | Low | Moderate |
| **Best For** | Point-to-point verification | Stateful verification |

---

## Key Principles

### 1. Separation of Concerns

**TB = Infrastructure:**
- Contains all BFMs and hardware interface code
- Provides reusable methods
- Used across multiple test scenarios
- Lives in `bin/CocoTBFramework/tbclasses/`

**Test = Intelligence:**
- Scenario-specific logic
- Calls TB methods
- Handles parametrization
- Lives in `val/{subsystem}/`

**Scoreboard = Verification:**
- Separate from TB and Test
- Chooses appropriate verification method (queue or memory)
- Independent verification logic
- Lives in `bin/CocoTBFramework/scoreboards/`

### 2. Use the Simplest Method That Works

**Don't over-engineer:**
- If queue access suffices, don't use a memory model
- If memory model is needed, use it without hesitation
- Match the verification complexity to the DUT complexity

**Examples:**
- Simple write: Queue access is perfect
- DMA with 1000 bursts: Memory model tracks state better

### 3. Verification Logic Belongs in Scoreboard

**Don't embed verification in TB:**
```python
# ❌ WRONG: Verification in TB
class MyTB(TBBase):
    async def test_write(self, addr, data):
        await self.send_write(addr, data)
        # Verification embedded here - WRONG!
        aw_pkt = self.aw_monitor._recvQ.popleft()
        assert aw_pkt.addr == addr

# ✅ CORRECT: Verification in scoreboard
class MyTB(TBBase):
    async def test_write(self, addr, data):
        self.scoreboard.expect_write(addr, data)
        await self.send_write(addr, data)
        return self.scoreboard.verify()
```

### 4. Clear State Between Test Sections

**Always clear queues/state after verification:**
```python
# After each test section
self.scoreboard.verify_section()
self.scoreboard.clear_queues()  # Prevent buildup

# Or if using memory model
self.scoreboard.verify_data(addr, expected)
self.scoreboard.reset()  # Clear for next section
```

---

## Implementation Checklist

When creating a new testbench, follow this checklist:

### TB Class (`tbclasses/{subsystem}/{module}_tb.py`)
- [ ] Inherits from `TBBase`
- [ ] Has `__init__()` that creates BFMs and scoreboard
- [ ] Implements `setup_clocks_and_reset()`
- [ ] Implements `assert_reset()` and `deassert_reset()`
- [ ] Provides base test methods (e.g., `run_basic_test()`)
- [ ] Does NOT contain verification logic
- [ ] Located in `bin/CocoTBFramework/tbclasses/`

### Scoreboard (`scoreboards/{subsystem}/{module}_scoreboard.py`)
- [ ] Separate class in scoreboards directory
- [ ] Takes monitors as constructor arguments
- [ ] Implements appropriate verification method:
  - [ ] Queue access for simple scenarios
  - [ ] Memory model for complex scenarios
- [ ] Has `expect_*()` methods to record expectations
- [ ] Has `verify_*()` methods to check results
- [ ] Has `clear_queues()` or `reset()` for state management
- [ ] Located in `bin/CocoTBFramework/scoreboards/`

### Test Runner (`val/{subsystem}/test_{module}.py`)
- [ ] Imports TB from `CocoTBFramework.tbclasses`
- [ ] Has CocoTB test functions (prefixed `cocotb_`)
- [ ] Has pytest wrappers with parametrization
- [ ] Calls TB methods (does NOT implement infrastructure)
- [ ] Located in `val/{subsystem}/`

---

## Examples by Subsystem

### Common Subsystem Example

**Simple FIFO verification (queue access):**
```python
# bin/CocoTBFramework/scoreboards/common/fifo_scoreboard.py
class FIFOScoreboard:
    """Simple FIFO verification using queue access"""

    def __init__(self, write_monitor, read_monitor):
        self.write_monitor = write_monitor
        self.read_monitor = read_monitor
        self.expected_data = []

    def record_write(self, data):
        """Record expected data"""
        self.expected_data.append(data)

    def verify_read(self):
        """Verify FIFO read matches expected"""
        if self.read_monitor._recvQ:
            read_pkt = self.read_monitor._recvQ.popleft()
            expected = self.expected_data.pop(0)
            return read_pkt.data == expected
        return False
```

### AMBA Subsystem Example

**APB monitor verification (queue access):**
```python
# bin/CocoTBFramework/scoreboards/amba/apb_scoreboard.py
class APBScoreboard:
    """APB transaction verification using queue access"""

    def __init__(self, apb_monitor):
        self.apb_monitor = apb_monitor
        self.expected_transactions = []

    def expect_write(self, addr, data):
        """Record expected APB write"""
        self.expected_transactions.append({
            'type': 'write',
            'addr': addr,
            'data': data
        })

    def verify_transaction(self):
        """Verify APB transaction"""
        if self.apb_monitor._recvQ:
            txn = self.apb_monitor._recvQ.popleft()
            expected = self.expected_transactions.pop(0)

            return (txn.addr == expected['addr'] and
                    txn.data == expected['data'])
        return False
```

### RAPIDS Subsystem Example

**Data path verification (memory model):**
```python
# bin/CocoTBFramework/scoreboards/rapids/sink_data_path_scoreboard.py
class SinkDataPathScoreboard:
    """Sink data path verification using memory model

    Uses memory model because:
    - Streaming data with multiple bursts
    - Need to track data integrity across transfers
    - Multi-beat AXI transactions
    """

    def __init__(self, aw_monitor, w_monitor):
        self.aw_monitor = aw_monitor
        self.w_monitor = w_monitor
        self.memory_model = MemoryModel(size=0x100000)
        self.expected_data = {}

    def expect_data(self, addr, data_list):
        """Record expected data at address"""
        self.expected_data[addr] = data_list

    async def process_writes(self):
        """Process write transactions and update memory"""
        while self.aw_monitor._recvQ:
            aw_pkt = self.aw_monitor._recvQ.popleft()

            # Process all data beats
            for i in range(aw_pkt.len + 1):
                w_pkt = self.w_monitor._recvQ.popleft()
                self.memory_model.write(
                    aw_pkt.addr + i * (aw_pkt.size),
                    w_pkt.data
                )

    def verify_data_integrity(self):
        """Verify all expected data is in memory"""
        for addr, expected_list in self.expected_data.items():
            for i, expected in enumerate(expected_list):
                actual = self.memory_model.read(addr + i * 4)
                if actual != expected:
                    return False
        return True
```

---

## Migration Guide

### Updating Existing Testbenches

If you have existing testbenches that don't follow this pattern:

#### Step 1: Extract Verification Logic

```python
# Before (verification in TB)
class MyTB(TBBase):
    async def test_operation(self, addr, data):
        await self.send_request(addr, data)
        # Verification embedded here
        pkt = self.monitor._recvQ.popleft()
        assert pkt.data == data

# After (verification in scoreboard)
# 1. Create scoreboard class
class MyScoreboard:
    def __init__(self, monitor):
        self.monitor = monitor

    def verify_transaction(self, expected_data):
        if self.monitor._recvQ:
            pkt = self.monitor._recvQ.popleft()
            return pkt.data == expected_data
        return False

# 2. Use scoreboard in TB
class MyTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.scoreboard = MyScoreboard(self.monitor)

    async def test_operation(self, addr, data):
        await self.send_request(addr, data)
        return self.scoreboard.verify_transaction(data)
```

#### Step 2: Choose Verification Method

Evaluate each verification point:
- Control path? → Queue access
- Data path? → Memory model

#### Step 3: Move Scoreboard to Separate File

```bash
# Create scoreboard directory if needed
mkdir -p bin/CocoTBFramework/scoreboards/{subsystem}/

# Move scoreboard class to separate file
# bin/CocoTBFramework/scoreboards/{subsystem}/{module}_scoreboard.py
```

#### Step 4: Update TB to Use Scoreboard

```python
# Import scoreboard
from CocoTBFramework.scoreboards.{subsystem}.{module}_scoreboard import MyScoreboard

class MyTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        # Create scoreboard
        self.scoreboard = MyScoreboard(self.monitor)
```

---

## Common Mistakes to Avoid

### ❌ Mistake 1: Verification Logic in TB

```python
# WRONG
class MyTB(TBBase):
    async def send_and_verify(self, addr, data):
        await self.send(addr, data)
        pkt = self.monitor._recvQ.popleft()  # Verification in TB!
        assert pkt.data == data
```

**Fix:** Move verification to scoreboard

### ❌ Mistake 2: Using Memory Model for Simple Control

```python
# WRONG (overkill for simple control)
class ControlScoreboard:
    def __init__(self):
        self.memory = MemoryModel()  # Unnecessary for simple writes
```

**Fix:** Use direct queue access for control paths

### ❌ Mistake 3: Using Queue Access for Complex Data

```python
# WRONG (insufficient for data path)
class DataPathScoreboard:
    def verify_burst(self):
        # How do you track 1000 beats across multiple bursts?
        pkt = self.monitor._recvQ.popleft()  # Too simple!
```

**Fix:** Use memory model for data paths

### ❌ Mistake 4: Not Clearing State

```python
# WRONG
def run_test_section(self):
    self.verify_operations()
    # Queue keeps growing, no clear!
```

**Fix:** Always clear queues/state between sections

---

## Summary

### Quick Reference

| Component | Location | Purpose | Contains |
|-----------|----------|---------|----------|
| **TB Class** | `tbclasses/{subsystem}/` | Infrastructure | BFMs, clocks, base methods |
| **Scoreboard** | `scoreboards/{subsystem}/` | Verification | Queue access OR memory model |
| **Test** | `val/{subsystem}/` | Intelligence | Scenarios, pytest wrappers |

### Verification Method Decision

| Scenario | Use |
|----------|-----|
| Control path | Queue access |
| Data path | Memory model |
| Single-master | Queue access |
| Multi-master | Memory model |
| In-order | Queue access |
| Out-of-order | Memory model |
| No address overlap | Queue access |
| Address overlap | Memory model |

### Remember

1. **Separate concerns**: TB ≠ Scoreboard ≠ Test
2. **Right tool for job**: Queue access for simple, memory model for complex
3. **Verification in scoreboard**: Never embed in TB
4. **Clear state**: Always clean up between sections

---

**Document Version:** 1.0
**Last Updated:** 2025-10-14
**Maintained By:** RTL Design Sherpa Project
**Applies To:** All subsystems (Common, AMBA, RAPIDS, etc.)
