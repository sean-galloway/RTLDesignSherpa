# Claude Code Guide: CocoTB Framework

**Version:** 1.0
**Last Updated:** 2025-10-13
**Purpose:** AI-specific guidance for working with bin/CocoTBFramework/ infrastructure

---

## Quick Context

**What:** Reusable CocoTB verification infrastructure for RTL testing
**Structure:** 196 Python files providing BFMs, testbenches, and utilities
**Your Role:** Help users leverage existing components and create scalable testbenches

---

## 📖 Global Requirements Reference

**IMPORTANT: Review `/GLOBAL_REQUIREMENTS.md` for mandatory testbench standards**

This file focuses on CocoTB framework usage. For all mandatory requirements:
- **See:** `/GLOBAL_REQUIREMENTS.md` - Consolidated mandatory requirements
- **Key Sections:** Testbench Architecture, Test Standards, Framework Usage
- **Compliance:** TB location, three methods, TBBase inheritance, three-layer architecture all MANDATORY

This CLAUDE.md provides framework-specific patterns. Also review:
- Root `/CLAUDE.md` - Repository-wide guidance
- `projects/components/CLAUDE.md` - Project area standards
- `projects/components/{name}/CLAUDE.md` - Component-specific TB requirements

---

## Framework Architecture

```
bin/CocoTBFramework/
├── components/           # Protocol-specific BFMs and drivers
│   ├── axi4/            # AXI4 master/slave, monitors, utilities
│   ├── axil4/           # AXI4-Lite drivers and monitors
│   ├── apb/             # APB drivers, monitors, utilities
│   ├── axis4/           # AXI-Stream components
│   ├── rapids/            # RAPIDS-specific BFMs (DataMoverBFM, etc.)
│   └── shared/          # Common protocol utilities
│
├── tbclasses/           # Reusable testbench classes
│   ├── amba/            # AMBA protocol testbenches
│   ├── rapids/            # RAPIDS subsystem testbenches
│   ├── shared/          # Base classes and utilities
│   │   ├── tbbase.py    # TBBase - foundation for all testbenches
│   │   └── utilities.py # Common helper functions
│   └── [subsystem]/     # Additional subsystem testbenches
│
└── scoreboards/         # Transaction verification
    ├── generic/         # Protocol-agnostic scoreboards
    └── [protocol]/      # Protocol-specific scoreboards
```

---

## Critical Rules for This Framework

### Rule #1: Search Before Creating (MANDATORY)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 4.1 for complete requirement

**Framework-Specific Search Commands:**

```bash
# Search for existing protocol components
find bin/CocoTBFramework/components/ -name "*.py" | xargs grep -l "class.*BFM"
find bin/CocoTBFramework/components/ -name "*.py" | xargs grep -l "class.*Master"
find bin/CocoTBFramework/components/ -name "*.py" | xargs grep -l "class.*Slave"

# Search for existing testbench base classes
find bin/CocoTBFramework/tbclasses/ -name "*_tb.py"

# Find usage examples
grep -r "from CocoTBFramework.components.axi4" val/
```

**Framework BFM Extraction Criteria:**

| Factor | Extract to Framework | Keep in Project Area |
|--------|---------------------|---------------------|
| Lines of code | >100 lines | <50 lines |
| Protocol | Standard (AXI4, APB, AXIS) | Project-specific |
| Reusability | Used across 3+ projects | Single project only |

---

### Rule #2: TBBase Inheritance (MANDATORY)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 2.3 for complete requirement

**Framework-Specific:** TBBase location and capabilities

```python
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

class MyModuleTB(TBBase):
    """Inherits: clock mgmt, reset, logging, utilities"""
    def __init__(self, dut):
        super().__init__(dut)
```

**TBBase API:** See `bin/CocoTBFramework/tbclasses/shared/tbbase.py`

---

### Rule #3: Three Mandatory Methods (MANDATORY)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 2.2 for complete requirement

**Framework Pattern:**
```python
async def setup_clocks_and_reset(self):
    await self.start_clock('clk', freq=10, units='ns')
    await self.assert_reset()
    await self.wait_clocks('clk', 10)
    await self.deassert_reset()

async def assert_reset(self):
    self.dut.rst_n.value = 0

async def deassert_reset(self):
    self.dut.rst_n.value = 1
```

---

### Rule #4: Three-Layer Architecture (MANDATORY)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 2.4 for complete requirement

**Framework-Specific Locations:**
- **Layer 1 (TB):** `bin/CocoTBFramework/tbclasses/{protocol}/` OR `projects/components/{name}/dv/tbclasses/`
- **Layer 2 (Test):** `val/{subsystem}/test_{module}.py` OR `projects/components/{name}/dv/tests/`
- **Layer 3 (Scoreboard):** `bin/CocoTBFramework/scoreboards/{protocol}/`

**Key:** Project-specific TBs go in project area, shared TBs go in framework.

---

### Rule #5: Queue-Based Verification (PREFERRED)

**📖 See:** `/GLOBAL_REQUIREMENTS.md` Section 2.5 for complete requirement

**Framework Scoreboard Example:**

```python
class SimpleScorebor:
    """Framework scoreboard pattern"""
    def __init__(self, monitor):
        self.monitor = monitor

    def check_transaction(self, expected_data):
        """Direct queue access"""
        if self.monitor._recvQ:
            pkt = self.monitor._recvQ.popleft()
            assert pkt.data == expected_data
            return True
        return False

    def clear_queues(self):
        """Clear after verification section"""
        self.monitor._recvQ.clear()
```

**When to Use Memory Models:** Complex OOO, multi-master overlap, or data paths tracking state.

**See:** `docs/VERIFICATION_ARCHITECTURE_GUIDE.md` for decision tree

---

## Component Usage Patterns

### Pattern: Using Existing AXI4 Components

```python
# ❌ WRONG: Creating new AXI4 implementation
class MyCustomAXI4Master:
    """Don't do this - AXI4 components already exist!"""
    async def write_transaction(self, addr, data):
        # 500+ lines of AXI4 protocol implementation...

# ✅ CORRECT: Use existing components
from CocoTBFramework.components.axi4.axi_master import AXI4Master

class MyTestbench(TBBase):
    def __init__(self, dut):
        super().__init__(dut)

        # Use existing AXI4 master
        self.axi_master = AXI4Master(
            dut=dut,
            name="axi_m",
            clock=dut.aclk
        )

    async def write_to_memory(self, addr, data):
        """Use framework's AXI4 master"""
        await self.axi_master.write(addr, data)
```

### Pattern: Simple Test-Specific Responders

**When framework components are too heavy for simple test needs:**

```python
class DescriptorEngineTB(TBBase):
    async def axi_read_responder(self):
        """Simple test-specific AXI read responder (50 lines)"""
        while True:
            await self.wait_clocks(self.clk_name, 1)

            # Minimal AXI read protocol for this specific test
            if int(self.dut.ar_valid.value) == 1:
                # Generate response
                self.dut.r_valid.value = 1
                self.dut.r_data.value = response_data
                # ... minimal handshaking ...
                self.dut.r_valid.value = 0
```

**When to Use:**
- ✅ Test-specific simulation (<50 lines)
- ✅ Simplified protocol subset
- ✅ Framework component would be overkill
- ❌ Complex protocol implementation (use framework)
- ❌ Reusable across multiple tests (extract to BFM)

### Pattern: Continuous Background Monitoring

**Problem:** Asynchronous outputs missed if checked only at specific points

**Solution:** Background monitoring coroutines

```python
class MyTestbench(TBBase):
    async def run_test_with_monitoring(self, num_operations):
        """Test with continuous output monitoring"""
        outputs_collected = []
        monitor_active = True

        # Background monitor coroutine
        async def output_monitor():
            """Continuously monitors output_valid every cycle"""
            while monitor_active:
                await self.wait_clocks(self.clk_name, 1)
                if int(self.dut.output_valid.value) == 1:
                    data = int(self.dut.output_data.value)
                    outputs_collected.append(data)
                    self.log.info(f"Captured output: 0x{data:X}")

        # Start background monitor
        monitor_task = cocotb.start_soon(output_monitor())

        # Perform test operations (monitor captures in background)
        for i in range(num_operations):
            await self.send_request(i)
            # Outputs captured automatically by background monitor

        # Wait for all outputs
        for _ in range(final_wait_cycles):
            await self.wait_clocks(self.clk_name, 1)
            if len(outputs_collected) >= num_operations:
                break

        # Stop monitor
        monitor_active = False
        await self.wait_clocks(self.clk_name, 2)

        # Verify 100% success
        return len(outputs_collected) == num_operations
```

**Key Elements:**
1. **Shared state:** `outputs_collected` list
2. **Control flag:** `monitor_active` for clean shutdown
3. **Background task:** `cocotb.start_soon()`
4. **Every-cycle monitoring:** Never miss outputs
5. **Clean shutdown:** Stop monitor, wait for completion

**When to Use:**
- ✅ Asynchronous output interfaces
- ✅ Pipelined designs with variable latency
- ✅ Rapid-fire input operations
- ✅ Multi-stage data flows

**Benefits:**
- 100% capture rate (no missed transactions)
- Decouples stimulus from response monitoring
- Realistic timing coverage

---

## BFM Creation Guidelines

### When to Create New BFM

**Create BFM in `components/[subsystem]/` when:**

| Criteria | Threshold |
|----------|-----------|
| Lines of code | >100 lines |
| Complexity | Complex protocol logic |
| Reusability | Used in 3+ tests |
| Scope | Subsystem-specific (not standard protocol) |
| Independence | Can be tested standalone |

**Example: DataMoverBFM**
```python
# File: bin/CocoTBFramework/components/rapids/data_mover_bfm.py

class DataMoverBFM:
    """
    Reusable BFM for RAPIDS data mover protocol simulation.

    Used across:
    - Scheduler tests (val/rapids/fub_tests/scheduler/)
    - Integration tests (val/rapids/integration_tests/)
    - System tests (val/rapids/system_tests/)

    150+ lines of RAPIDS-specific data mover logic.
    """

    def __init__(self, dut, clock):
        self.dut = dut
        self.clock = clock

    async def send_data(self, address, data, **kwargs):
        """Send data via RAPIDS data mover protocol"""
        # Complex RAPIDS-specific protocol implementation...

    async def receive_data(self, **kwargs):
        """Receive data via RAPIDS data mover protocol"""
        # Complex RAPIDS-specific protocol implementation...
```

### When to Keep Embedded

**Keep in testbench when:**

| Criteria | Threshold |
|----------|-----------|
| Lines of code | <50 lines |
| Complexity | Simple stimulus/response |
| Reusability | Test-specific, not reusable |
| Scope | Standard protocol (framework exists) |
| Integration | Tightly coupled to one test |

---

## Test Scalability Patterns

### Pattern: Delay Profiles for Timing Coverage

```python
from enum import Enum

class DelayProfile(Enum):
    """Configurable delay profiles for timing coverage"""
    FAST_PRODUCER = "fast_producer"
    FAST_CONSUMER = "fast_consumer"
    FIXED_DELAY = "fixed_delay"
    MINIMAL_DELAY = "minimal_delay"
    BACKPRESSURE = "backpressure"

class MyTestbench(TBBase):
    def __init__(self, dut):
        super().__init__(dut)

        # Define profile parameters
        self.delay_params = {
            DelayProfile.FAST_PRODUCER: {
                'producer_delay': (1, 3),
                'consumer_delay': (5, 15),
                'backpressure_freq': 0.1
            },
            DelayProfile.MINIMAL_DELAY: {
                'producer_delay': 1,
                'consumer_delay': 1,
                'backpressure_freq': 0.3
            },
            # ... other profiles
        }

    async def run_test(self, num_ops, profile: DelayProfile):
        """Scalable test with configurable timing"""
        params = self.delay_params[profile]

        for i in range(num_ops):
            # Apply profile-specific delays
            delay = self.get_delay_value(params['producer_delay'])
            await self.wait_clocks(self.clk_name, delay)

            # Send operation
            await self.send_operation(i)

            # Profile-specific backpressure
            if random.random() < params['backpressure_freq']:
                await self.wait_clocks(self.clk_name, random.randint(5, 25))
```

### Pattern: Hierarchical Test Levels

```python
# Test runner with multiple complexity levels
@pytest.mark.parametrize("test_level", ["basic", "medium", "full"])
def test_my_module(test_level, ...):
    """Hierarchical test levels"""

    if test_level == "basic":
        # Quick smoke test: minimal operations, simple timing
        num_ops = 10
        profiles = [DelayProfile.FIXED_DELAY]

    elif test_level == "medium":
        # Moderate coverage: more operations, multiple profiles
        num_ops = 50
        profiles = [DelayProfile.FAST_PRODUCER, DelayProfile.FAST_CONSUMER]

    elif test_level == "full":
        # Comprehensive: maximum operations, all profiles
        num_ops = 100
        profiles = list(DelayProfile)

    # Run test with selected level
    # ...
```

---

## Test Success Criteria

### ⚠️ CRITICAL: 100% Success Required

**All tests MUST achieve 100% success rate - no exceptions.**

```python
# ❌ WRONG: Accepting partial success
def verify_results(expected, actual):
    success_rate = (actual / expected) * 100
    return success_rate >= 70  # "Mostly good" - NOT ACCEPTABLE!

# ✅ CORRECT: Require 100% success
def verify_results(expected, actual):
    success_rate = (actual / expected) * 100
    if success_rate < 100:
        self.log.error(f"FAIL: {actual}/{expected} ({success_rate:.1f}%)")
        return False
    self.log.info(f"PASS: {actual}/{expected} (100.0%)")
    return True
```

**Rationale:**
- RTL is deterministic - 100% success is achievable
- Partial success indicates bugs or timing issues
- Lower thresholds mask real problems
- Tests must reliably catch regressions

**Example Results:**
- ❌ Before fix: 5/12 descriptors (42%) - UNACCEPTABLE
- ✅ After fix: 14/14 tests passing (100%) - REQUIRED STANDARD

---

## Common Utilities (TBBase)

### Clock Management

```python
# Start clock
await self.start_clock('clk', freq=10, units='ns')

# Wait for clock cycles
await self.wait_clocks('clk', 5)

# Wait for condition with timeout
await self.wait_for_signal(signal, value=1, timeout_cycles=100)
```

### Reset Management

```python
# Full reset sequence
await self.setup_clocks_and_reset()

# Individual reset control
await self.assert_reset()
await self.wait_clocks('clk', 10)
await self.deassert_reset()
```

### Logging

```python
# Standard logging
self.log.info("Test started")
self.log.debug(f"Signal value: {signal_value}")
self.log.error("Unexpected condition")

# Progress tracking
self.mark_progress("initialization_complete")
self.mark_progress("operation_complete")
```

### Utilities

```python
# Convert environment variables
num_channels = self.convert_to_int(os.environ.get('NUM_CHANNELS', '32'))

# Format for test names (TBBase.format_dec())
test_id = TBBase.format_dec(channel_id, 2)  # "08" not "8"
```

---

## Anti-Patterns to Avoid

### ❌ Anti-Pattern 1: Duplicating Standard Protocols

```python
❌ WRONG: Implementing AXI4/APB/AXIS from scratch
class MyAXI4Implementation:
    """200+ lines reimplementing AXI4 - DON'T DO THIS!"""

✅ CORRECT: Use framework components
from CocoTBFramework.components.axi4 import AXI4Master
```

### ❌ Anti-Pattern 2: Not Using TBBase

```python
❌ WRONG: Custom base class or no inheritance
class MyTestbench:
    """Missing all TBBase utilities!"""

✅ CORRECT: Inherit from TBBase
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

class MyTestbench(TBBase):
    """Inherits clock, reset, logging, utilities"""
```

### ❌ Anti-Pattern 3: Accepting Partial Success

```python
❌ WRONG:
assert success_rate >= 70  # "Good enough" - NO!

✅ CORRECT:
assert success_rate >= 100  # 100% required
```

### ❌ Anti-Pattern 4: Missing Monitoring

```python
❌ WRONG: Only checking outputs at end
for i in range(num_ops):
    send_operation(i)
# Check outputs here - TOO LATE! Some missed

✅ CORRECT: Continuous background monitoring
async def monitor():
    while active:
        if output_valid: collect()
monitor_task = cocotb.start_soon(monitor())
```

---

## Examples and References

### Example Testbenches

**AMBA Examples:**
- `bin/CocoTBFramework/tbclasses/amba/apb_slave_tb.py` - APB slave testing
- `bin/CocoTBFramework/tbclasses/amba/axi4_monitor_tb.py` - AXI4 monitoring

**RAPIDS Examples:**
- `bin/CocoTBFramework/tbclasses/rapids/scheduler_tb.py` - Scheduler with DataMoverBFM
- `bin/CocoTBFramework/tbclasses/rapids/descriptor_engine_tb.py` - Continuous monitoring pattern

### Component Examples

**Standard Protocols:**
- `bin/CocoTBFramework/components/axi4/` - AXI4 masters, slaves, monitors
- `bin/CocoTBFramework/components/apb/` - APB drivers and monitors

**Custom BFMs:**
- `bin/CocoTBFramework/components/rapids/data_mover_bfm.py` - RAPIDS data mover protocol

---

## Quick Reference

### Finding Existing Components

```bash
# List all BFMs
find bin/CocoTBFramework/components/ -name "*bfm.py"

# List all testbench classes
find bin/CocoTBFramework/tbclasses/ -name "*_tb.py"

# Search for protocol usage
grep -r "class.*Master" bin/CocoTBFramework/components/
grep -r "class.*Driver" bin/CocoTBFramework/components/
```

### Common Imports

```python
# Base class (ALWAYS)
from CocoTBFramework.tbclasses.shared.tbbase import TBBase

# Utilities
from CocoTBFramework.tbclasses.shared.utilities import get_paths, create_view_cmd

# Protocol components
from CocoTBFramework.components.axi4.axi_master import AXI4Master
from CocoTBFramework.components.apb.apb_driver import APBDriver

# RAPIDS-specific
from CocoTBFramework.components.rapids.data_mover_bfm import DataMoverBFM
```

---

## Remember

1. 🔍 **Search first** - Components likely exist, don't duplicate
2. 🏗️ **Inherit TBBase** - All testbenches must inherit from TBBase
3. ⚙️ **Three mandatory methods** - setup_clocks_and_reset, assert_reset, deassert_reset
4. 🎯 **Continuous monitoring** - Use background coroutines for asynchronous outputs
5. 📊 **100% success** - All tests must achieve 100% success rate
6. 📦 **BFM criteria** - Extract when >100 lines, reusable, subsystem-specific
7. 🚫 **Don't reimplement** - Use existing AXI4/APB/AXIS components
8. 📈 **Test scalability** - Support basic/medium/full test levels
9. 🏛️ **Three-layer architecture** - TB (infrastructure) + Test (intelligence) + Scoreboard (verification)
10. 🎪 **Queue-based verification** - Use `monitor._recvQ.popleft()` for simple tests, not memory models

---

**Version:** 1.1
**Last Updated:** 2025-10-14
**Maintained By:** RTL Design Sherpa Project
