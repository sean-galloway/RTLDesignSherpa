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

# 5.1 Test Strategy

This section describes the verification approach for converter modules.

## 5.1.1 Test Organization

### Test Hierarchy

```
projects/components/converters/dv/tests/
├── width_converters/
│   ├── test_axi_data_upsize.py
│   ├── test_axi_data_dnsize.py
│   ├── test_axi4_dwidth_converter_wr.py
│   └── test_axi4_dwidth_converter_rd.py
├── protocol_converters/
│   ├── test_axi4_to_axil4_rd.py
│   ├── test_axi4_to_axil4_wr.py
│   ├── test_axil4_to_axi4_rd.py
│   ├── test_axil4_to_axi4_wr.py
│   ├── test_axi4_to_apb.py
│   └── test_peakrdl_adapter.py
└── integration/
    ├── test_width_protocol_chain.py
    └── test_full_system.py
```

## 5.1.2 Test Levels

### Level 1: Unit Tests

**Purpose:** Verify individual module functionality in isolation.

**Coverage:**
- All parameters combinations
- Edge cases (min/max values)
- Error injection

**Example:**
```python
@pytest.mark.parametrize("narrow_width,wide_width", [
    (32, 64),
    (32, 128),
    (64, 256),
    (64, 512),
    (128, 1024),
])
async def test_upsize_ratios(dut, narrow_width, wide_width):
    """Test various width ratios."""
    tb = UpsizeTB(dut, narrow_width, wide_width)
    await tb.reset()
    await tb.run_basic_transfer(count=100)
    assert tb.scoreboard.check_passed()
```

### Level 2: Integration Tests

**Purpose:** Verify module combinations work together.

**Coverage:**
- Width converter + protocol converter chains
- Back-to-back converters
- Mixed traffic patterns

### Level 3: System Tests

**Purpose:** Verify in realistic system context.

**Coverage:**
- CPU-to-DDR paths
- Peripheral access paths
- Full bandwidth stress

## 5.1.3 Test Categories

### Functional Tests

| Category | Description | Example |
|----------|-------------|---------|
| Basic | Single transactions | Single read, single write |
| Burst | Multi-beat transactions | INCR burst, WRAP burst |
| Mixed | Interleaved R/W | Read-modify-write sequences |
| Edge | Boundary conditions | Max burst length, min width |

: Table 5.1: Functional Test Categories

### Stress Tests

| Category | Description | Duration |
|----------|-------------|----------|
| Throughput | Maximum bandwidth | 10,000 transactions |
| Backpressure | Ready signal variations | Random delays |
| Reset | Reset during operation | Mid-transaction reset |

: Table 5.2: Stress Test Categories

### Error Tests

| Category | Description | Expected Behavior |
|----------|-------------|-------------------|
| SLVERR | Slave error injection | Error propagation |
| DECERR | Decode error | Error response |
| Timeout | Response timeout | Error handling |

: Table 5.3: Error Test Categories

## 5.1.4 Testbench Architecture

### Components

```
Testbench
├── Drivers
│   ├── AXI4 Master Driver
│   ├── AXI4 Slave Driver
│   ├── AXIL4 Master/Slave
│   └── APB Master/Slave
├── Monitors
│   ├── AXI4 Monitor
│   ├── AXIL4 Monitor
│   └── APB Monitor
├── Scoreboard
│   ├── Transaction Queue
│   ├── Response Checker
│   └── Coverage Collector
└── Generators
    ├── Random Transaction Generator
    └── Directed Sequence Generator
```

### Driver Implementation

```python
class AXI4MasterDriver:
    def __init__(self, dut, clock, prefix="s_axi"):
        self.dut = dut
        self.clock = clock
        self.prefix = prefix

    async def write(self, addr, data, burst_len=0):
        """Issue AXI4 write transaction."""
        # AW phase
        self.dut.awvalid.value = 1
        self.dut.awaddr.value = addr
        self.dut.awlen.value = burst_len
        await self._wait_ready("awready")

        # W phase
        for i, d in enumerate(data):
            self.dut.wvalid.value = 1
            self.dut.wdata.value = d
            self.dut.wlast.value = (i == len(data) - 1)
            await self._wait_ready("wready")

        # B phase
        await self._wait_valid("bvalid")
        return self.dut.bresp.value
```

## 5.1.5 Coverage Model

### Functional Coverage

```python
@coverage
class ConverterCoverage:
    # Width ratio coverage
    ratio_cp = coverpoint(
        lambda: self.width_ratio,
        bins=[2, 4, 8, 16]
    )

    # Burst length coverage
    burst_len_cp = coverpoint(
        lambda: self.burst_len,
        bins=list(range(0, 256, 16)) + [255]
    )

    # Burst type coverage
    burst_type_cp = coverpoint(
        lambda: self.burst_type,
        bins=["FIXED", "INCR", "WRAP"]
    )

    # Cross coverage
    ratio_x_burst = cross(ratio_cp, burst_len_cp)
```

### Code Coverage

**Target:** >95% line coverage, >90% branch coverage

| Module | Line | Branch | FSM |
|--------|------|--------|-----|
| axi_data_upsize | 98% | 95% | 100% |
| axi_data_dnsize | 97% | 93% | 100% |
| axi4_to_axil4_rd | 96% | 91% | 100% |
| axi4_to_axil4_wr | 95% | 90% | 100% |

: Table 5.4: Coverage Targets

## 5.1.6 Test Execution

### Running Tests

```bash
# Run all converter tests
cd projects/components/converters/dv/tests
pytest -v

# Run specific module tests
pytest test_axi_data_upsize.py -v

# Run with coverage
pytest --cov=projects/components/converters/rtl -v

# Run with waveform dump
pytest test_axi_data_upsize.py -v --waves
```

### CI/CD Integration

```yaml
converter_tests:
  stage: test
  script:
    - cd projects/components/converters/dv/tests
    - pytest -v --junitxml=results.xml
    - pytest --cov=rtl --cov-report=html
  artifacts:
    reports:
      junit: results.xml
    paths:
      - htmlcov/
```

---

**Next:** [Debug Guide](02_debug_guide.md)
