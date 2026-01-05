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

## Factory-Based Testing

### BFM Instantiation

```python
from CocoTBFramework.components.gaxi import GAXIMaster, GAXISlave

class BridgeTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)

        # Create masters using factory pattern
        self.masters = []
        for i in range(NUM_MASTERS):
            prefix = f"m{i}_axi_"
            master = GAXIMaster(
                dut=dut,
                prefix=prefix,
                clock=dut.aclk,
                reset=dut.aresetn
            )
            self.masters.append(master)

        # Create slaves
        self.slaves = []
        for i in range(NUM_SLAVES):
            prefix = f"s{i}_axi_"
            slave = GAXISlave(
                dut=dut,
                prefix=prefix,
                clock=dut.aclk,
                reset=dut.aresetn
            )
            self.slaves.append(slave)
```

### Transaction Generation

```python
async def test_concurrent_writes(self):
    """Test multiple masters writing simultaneously."""

    # Generate transactions for each master
    tasks = []
    for i, master in enumerate(self.masters):
        addr = 0x1000 + (i * 0x100)
        data = [0xDEAD0000 + i] * 4
        task = cocotb.start_soon(
            master.write(addr=addr, data=data, size=2)
        )
        tasks.append(task)

    # Wait for all to complete
    for task in tasks:
        await task

    # Verify arbitration occurred correctly
    self.verify_arbitration_order()
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

### Running Tests

```bash
# Run all bridge tests
cd projects/components/bridge/dv/tests
pytest -v

# Run specific configuration
pytest test_bridge_4x4.py -v

# Run with coverage
pytest --cov=bridge -v

# Run with waveforms
WAVES=1 pytest test_bridge_2x2.py -v
```

### Test Levels

| Level | Duration | Coverage | Use Case |
|-------|----------|----------|----------|
| basic | ~30s | Smoke test | Quick verification |
| medium | ~90s | Core paths | Development |
| full | ~180s | Comprehensive | Pre-commit |

: Table 7.2: Test Level Definitions

## Related Documentation

- [Debug Guide](02_debug_guide.md) - Debugging failed tests
- [Signal Naming](../ch06_generated_rtl/02_signal_naming.md) - Pattern matching for BFMs
