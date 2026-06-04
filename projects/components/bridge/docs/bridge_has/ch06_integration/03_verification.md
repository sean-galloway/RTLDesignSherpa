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

# Verification Strategy

## Verification Levels

### Unit Level

Test individual Bridge components:

| Component | Test Focus |
|-----------|------------|
| Master Adapter | Skid buffer, ID extension |
| Slave Router | Address decode, arbitration |
| Width Converter | Upsize/downsize correctness |
| Protocol Converter | AXI4 to APB timing |
| Response Router | ID extraction, routing |

: Table 6.13: Unit Level Test Focus

### Integration Level

Test complete Bridge functionality:

| Test Category | Coverage |
|---------------|----------|
| Address routing | All master-slave paths |
| Arbitration | Contention, fairness |
| ID tracking | Response routing |
| Error handling | OOR, timeouts |
| Performance | Throughput, latency |

: Table 6.14: Integration Test Coverage

### System Level

Test Bridge in target system:

| Test Category | Focus |
|---------------|-------|
| End-to-end | CPU to memory |
| Multi-master | DMA + CPU |
| Mixed protocol | AXI4 + APB |
| Stress | Maximum traffic |

: Table 6.15: System Level Tests

## Test Infrastructure

### CocoTB Framework with Protocol-BFM-Only Driving

Bridge uses CocoTB for verification with a protocol-BFM-only approach: **all test stimulus is driven through protocol BFMs (AXI4Master, AXI4Slave, etc.) with no direct DUT signal manipulation**. Each slave port is backed by an in-memory model (`MemoryModel`), and verification is assertion-based (readback matches write) rather than routing-based.

```python
from CocoTBFramework.components.axi4 import AXI4Master, AXI4Slave
from TBClasses.shared.tbbase import TBBase

class BridgeTB(TBBase):
    def __init__(self, dut):
        super().__init__(dut)
        self.masters = [AXI4Master(dut, dut.clk, f"m{i}_axi") for i in range(NUM_MASTERS)]
        self.slaves = [MemoryModel(dut, dut.clk, f"s{i}_axi") for i in range(NUM_SLAVES)]

@cocotb.test()
async def cocotb_test_basic_write(dut):
    tb = BridgeTB(dut)
    await tb.setup_clocks_and_reset()

    # Write transaction via BFM only
    await tb.masters[0].write(addr=0x1000, data=0xDEADBEEF)
    
    # Verify: readback matches write (memory-model assertion)
    readback = await tb.masters[0].read(addr=0x1000)
    assert readback == 0xDEADBEEF
```

### Test Categories

| Category | Description | Example |
|----------|-------------|---------|
| Basic | Single transactions | Read/write |
| Burst | Multi-beat transactions | 16-beat burst |
| Concurrent | Multiple masters active | M0 + M1 |
| Boundary Probe | Address window edges | Top/mid/bottom of each slave page |
| Stress | Maximum utilization | Back-to-back |
| Error | Error conditions | SLVERR injection, timeout |
| Monitor | Monitor packet collection | Packet capture, IRQ assertion |

: Table 6.16: Test Categories

## Test Execution Model

### Serial Execution

Bridge tests run **serially only** (no parallel execution via pytest-xdist). Each test function is named per-module to avoid cross-test cocotb function name pollution:

```python
# Naming convention: test_bridge_{N}x{M}_{variant}_{scenario}
def test_bridge_1x2_rd_basic(request):        # Test name indicates 1 master, 2 slaves, read-only
def test_bridge_1x2_rd_monitor_smoke(request): # Monitor test on 1x2
def test_bridge_4x4_rw_concurrent(request):    # Concurrent test on 4x4
```

Cocotb test functions inside each file follow the same naming pattern but with `cocotb_test_*` prefix to avoid pytest collection conflicts.

### Boundary Probe Testing

Address-window boundary testing probes the **top, middle, and bottom** of each slave's address window to catch address-decode logic errors at window edges:

```python
for slave_idx, (base, window_size) in enumerate(slave_windows):
    # Probe bottom (base address)
    await master.write(base + 0x000, data)
    
    # Probe middle (arbitrary address within window)
    await master.write(base + window_size // 2, data)
    
    # Probe top (base + window_size - 1)
    await master.write(base + window_size - 1, data)
```

## Coverage Goals

### Functional Coverage

| Category | Target |
|----------|--------|
| Address paths | 100% master-slave combinations via boundary probes |
| Transaction types | Read, write, burst, error (SLVERR) |
| Monitor modes | Enabled and disabled |
| ID values | Full ID range (representative) |

: Table 6.17: Functional Coverage Goals

### Code Coverage

| Metric | Target |
|--------|--------|
| Line coverage | >95% |
| Branch coverage | >90% |
| FSM coverage | 100% state transitions |
| Toggle coverage | >80% signals |

: Table 6.18: Code Coverage Goals

## Debug Features

### Waveform Capture

Bridge tests support VCD/FST waveform dumps:

```bash
pytest test_bridge.py --vcd=waves.vcd
gtkwave waves.vcd
```

### Debug Signals

Bridge includes optional debug signals:

| Signal | Description |
|--------|-------------|
| dbg_aw_grant | Current AW grant |
| dbg_ar_grant | Current AR grant |
| dbg_outstanding | Outstanding transaction count |
| dbg_state | FSM states |

: Table 6.19: Debug Signals

## Regression Testing

### Continuous Integration

| Stage | Tests | Frequency |
|-------|-------|-----------|
| Pre-commit | Basic sanity | Each commit |
| Nightly | Full regression | Daily |
| Weekly | Performance | Weekly |

: Table 6.20: CI Test Schedule

### Test Matrix

| Config | Data Width | Protocol | Tested |
|--------|-----------|----------|--------|
| 2x2 | 64 | AXI4 | Yes |
| 4x4 | 64 | AXI4 | Yes |
| 4x4 | 256 | AXI4 | Yes |
| 2x2 | 64 | AXI4+APB | Yes |
| RAPIDS | 512 | AXI4+APB | Yes |

: Table 6.21: Configuration Test Matrix

## Known Limitations

### Test Gaps

| Gap | Status | Plan |
|-----|--------|------|
| APB burst stress | Partial | Phase 3 |
| Width downsize stress | Partial | Planned |
| 32-master config | Not tested | Low priority |

: Table 6.22: Known Test Gaps

### Simulator Support

| Simulator | Status |
|-----------|--------|
| Verilator | Fully supported |
| Icarus Verilog | Supported |
| Commercial (VCS, Questa) | Not tested |

: Table 6.23: Simulator Support Status
