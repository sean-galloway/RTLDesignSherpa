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

# Test Strategy

## Overview

Bridge verification uses CocoTB-based testing with parameterized configurations. The test infrastructure supports all bridge topologies and protocol combinations.

## Test Categories

### Unit Tests

Per-block verification:

```
Unit Test Coverage:
├── Master Adapter Tests
│   ├── ID extension verification
│   ├── Channel routing
│   └── Backpressure handling
├── Address Decoder Tests
│   ├── Address mapping
│   ├── Multi-region support
│   └── Default slave routing
├── Arbiter Tests
│   ├── Round-robin fairness
│   ├── Grant/lock behavior
│   └── Multi-master contention
└── Converter Tests
    ├── Width up/down sizing
    ├── APB protocol conversion
    └── Burst handling
```

### Integration Tests

Full bridge verification:

```
Integration Test Matrix:
├── 2x2 Configuration
│   ├── Basic read/write
│   ├── Concurrent transactions
│   └── ID collision avoidance
├── 4x4 Configuration
│   ├── Full arbitration coverage
│   ├── Width conversion paths
│   └── Mixed protocol targets
└── NxM Configurations
    ├── Asymmetric topologies
    ├── Channel-specific masters
    └── Protocol mixing
```

## Test Parameterization

### Configuration Matrix

| Parameter | Test Values | Purpose |
|-----------|-------------|---------|
| NUM_MASTERS | 2, 4, 8 | Scalability |
| NUM_SLAVES | 2, 3, 4 | Routing coverage |
| DATA_WIDTH | 32, 64, 128, 256 | Width paths |
| ID_WIDTH | 4, 6, 8 | ID space |
| OUTSTANDING | 4, 8, 16 | Depth stress |

: Table 7.1: Test Parameter Matrix

### Protocol Combinations

```python
# Test protocol matrix
PROTOCOL_COMBOS = [
    {"masters": ["axi4"], "slaves": ["axi4"]},
    {"masters": ["axi4"], "slaves": ["axi4", "apb"]},
    {"masters": ["axi4", "axil"], "slaves": ["axi4", "apb"]},
]
```

## Protocol-BFM-Only Testing with Memory-Backed Slaves

Modern bridge tests use **protocol BFMs only** (no direct DUT signal manipulation) with **memory-backed slave models**:

### BFM Instantiation and Slave Models

```python
from CocoTBFramework.components.axi4 import AXI4Master, AXI4Slave
from TBClasses.shared.tbbase import TBBase
from TBClasses.shared.memory_model import MemoryModel

class BridgeTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)

        # Create masters using protocol BFMs
        self.masters = []
        for i in range(NUM_MASTERS):
            prefix = f"m{i}_axi_"
            master = AXI4Master(
                dut=dut,
                prefix=prefix,
                clock=dut.aclk,
                reset=dut.aresetn
            )
            self.masters.append(master)

        # Create slave memory models (NOT direct signal manipulation)
        self.slaves = []
        for i in range(NUM_SLAVES):
            prefix = f"s{i}_axi_"
            slave = MemoryModel(
                dut=dut,
                prefix=prefix,
                clock=dut.aclk,
                reset=dut.aresetn,
                size=0x100000  # 1 MB memory per slave
            )
            self.slaves.append(slave)
```

### Transaction Generation and Assertion

```python
async def cocotb_test_concurrent_writes(dut):
    """Test multiple masters writing simultaneously."""
    tb = BridgeTB(dut)
    await tb.setup_clocks_and_reset()

    # Generate transactions via BFMs only
    tasks = []
    for i, master in enumerate(tb.masters):
        addr = 0x1000 + (i * 0x100)
        data = 0xDEAD0000 + i
        # Drive via protocol BFM (no DUT signal poke)
        task = cocotb.start_soon(
            master.write(addr=addr, data=data, size=2)
        )
        tasks.append(task)

    # Wait for all writes to complete
    for task in tasks:
        await task

    # Verify via memory readback (not via routing logic check)
    for i, master in enumerate(tb.masters):
        addr = 0x1000 + (i * 0x100)
        readback = await master.read(addr=addr)
        assert readback == 0xDEAD0000 + i, \
            f"Master {i} readback mismatch at {addr:#x}"
```

### Boundary Probe Testing

Address-window boundary probes catch address-decode errors at slave page edges:

```python
async def test_boundary_probes(self):
    """Probe top, middle, bottom of each slave's address window."""
    
    for slave_idx, (base_addr, window_size) in enumerate(self.slave_windows):
        # Probe bottom (base address)
        await self.masters[0].write(base_addr + 0x000, data=0xBOTTOM)
        
        # Probe middle (arbitrary offset)
        await self.masters[0].write(base_addr + window_size // 2, data=0xMIDDLE)
        
        # Probe top (last valid address)
        await self.masters[0].write(base_addr + window_size - 1, data=0xTOP)
        
        # Verify via readback
        rb_bottom = await self.masters[0].read(base_addr + 0x000)
        rb_middle = await self.masters[0].read(base_addr + window_size // 2)
        rb_top = await self.masters[0].read(base_addr + window_size - 1)
        
        assert rb_bottom == 0xBOTTOM
        assert rb_middle == 0xMIDDLE
        assert rb_top == 0xTOP
```

## Coverage Goals

### Functional Coverage

```
Coverage Targets:
├── Protocol Coverage
│   ├── All burst types (FIXED, INCR, WRAP)
│   ├── All sizes (1, 2, 4, 8, ... bytes)
│   └── All response types
├── Routing Coverage
│   ├── Every master to every slave path
│   ├── Default slave routing
│   └── Error response paths
├── Arbitration Coverage
│   ├── All grant combinations
│   ├── Priority scenarios
│   └── Lock sequences
└── Corner Cases
    ├── Maximum outstanding
    ├── ID exhaustion
    └── Backpressure saturation
```

### Code Coverage

```
Code Coverage Targets:
├── Line Coverage: >95%
├── Branch Coverage: >90%
├── FSM State Coverage: 100%
└── Toggle Coverage: >85%
```

## Test Execution

### Serial Execution (No Parallel xdist)

Bridge tests execute **serially only** (pytest-xdist parallelization is not supported). Each cocotb test function is named with a `cocotb_test_*` prefix to avoid cross-test name collisions when multiple test modules are loaded.

```bash
# Run all bridge tests (serial)
cd projects/components/bridge/dv/tests
pytest -v

# Run specific configuration test
pytest test_bridge_4x4_rw_basic.py -v

# Run with coverage
pytest --cov=bridge -v

# Run with waveforms
WAVES=1 pytest test_bridge_2x2_rd_basic.py -v
```

### Test Naming Convention

Cocotb test functions follow the pattern: `cocotb_test_{N}x{M}_{variant}_{scenario}`

```python
# Example: test_bridge_4x4_mon_capture.py
@cocotb.test()
async def cocotb_test_4x4_mon_capture(dut):
    """Monitor packet capture on 4x4 bridge with monitor enabled."""
    ...

# Pytest wrapper function
def test_bridge_4x4_mon_capture(request):
    """Wrapper to invoke cocotb_test_4x4_mon_capture."""
    run(
        python_search=[tests_dir],
        verilog_sources=verilog_sources,
        toplevel="bridge_4x4_mon",
        module=module,
        testcase="cocotb_test_4x4_mon_capture",
        ...
    )
```

### Test Levels and Variants

| Level | Duration | Coverage | Use Case |
|-------|----------|----------|----------|
| basic | ~30s | Smoke test (single transaction) | Quick verification |
| medium | ~90s | Core paths (concurrent, multi-slave) | Development |
| full | ~180s | Comprehensive (stress, boundary probes) | Pre-commit |
| monitor | ~120s | Monitor system validation | Monitor-specific scenarios |

: Table 7.2: Test Level and Variant Definitions

**Monitor Tests** (when `variants` includes `"mon"`):
- `test_bridge_1x2_rd_monitor_smoke`: Basic packet emission
- `test_bridge_1x2_rd_monitor_capture`: Packet parsing and verification
- `test_bridge_1x2_rd_monitor_error_inject`: SLVERR packet collection
- `test_bridge_1x2_rd_monitor_irq`: IRQ assertion on error FIFO

## Related Documentation

- [Debug Guide](02_debug_guide.md) - Debugging failed tests
- [Signal Naming](../ch06_generated_rtl/02_signal_naming.md) - Pattern matching for BFMs
