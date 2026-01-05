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

### CocoTB Framework

Bridge uses CocoTB for verification:

```python
from CocoTBFramework.components.axi4 import AXI4Master, AXI4Slave

@cocotb.test()
async def test_basic_write(dut):
    tb = BridgeTB(dut)
    await tb.setup_clocks_and_reset()

    # Write transaction
    await tb.master[0].write(addr=0x1000, data=0xDEADBEEF)

    # Verify
    assert tb.slave[0].mem[0x1000] == 0xDEADBEEF
```

### Test Categories

| Category | Description | Example |
|----------|-------------|---------|
| Basic | Single transactions | Read/write |
| Burst | Multi-beat transactions | 16-beat burst |
| Concurrent | Multiple masters active | M0 + M1 |
| Stress | Maximum utilization | Back-to-back |
| Error | Error conditions | OOR address |

: Table 6.16: Test Categories

## Coverage Goals

### Functional Coverage

| Category | Target |
|----------|--------|
| Address paths | 100% master-slave combinations |
| Transaction types | Read, write, burst |
| ID values | Full ID range |
| Data patterns | Walking 1s/0s, random |

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
