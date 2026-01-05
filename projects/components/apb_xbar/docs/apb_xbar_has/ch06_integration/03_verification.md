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

## Pre-Verified Component

The APB Crossbar is pre-verified with comprehensive tests:

| Variant | Test Transactions | Status |
|---------|-------------------|--------|
| apb_xbar_1to1 | 100+ | Pass |
| apb_xbar_2to1 | 130+ | Pass |
| apb_xbar_1to4 | 200+ | Pass |
| apb_xbar_2to4 | 350+ | Pass |

: Pre-Verification Status

## Test Categories

### Basic Connectivity

Tests for each variant include:
- Single read transaction to each slave
- Single write transaction to each slave
- Read-modify-write sequences
- All address regions exercised

### Address Decode Verification

For multi-slave variants:
- Verify each slave selected by correct address range
- Boundary address testing
- Invalid address behavior

### Arbitration Testing

For multi-master variants:
- Round-robin fairness verification
- Contention handling
- Grant persistence validation
- No starvation testing

### Stress Testing

High-intensity scenarios:
- Back-to-back transactions
- Random delays
- Mixed read/write patterns
- Concurrent multi-master access

## Integration Testing Recommendations

### Level 1: Basic Integration

| Test | Description | Pass Criteria |
|------|-------------|---------------|
| Reset test | Apply reset, verify outputs | All outputs at safe values |
| Single transaction | Read from each slave | Correct data returned |
| Write verify | Write and readback | Data matches |

: Level 1 Integration Tests

### Level 2: Functional Integration

| Test | Description | Pass Criteria |
|------|-------------|---------------|
| All masters | Each master accesses each slave | No errors |
| Arbitration | Concurrent master access | Fair grant rotation |
| Error propagation | Force PSLVERR from slave | Error reaches master |

: Level 2 Integration Tests

### Level 3: System Integration

| Test | Description | Pass Criteria |
|------|-------------|---------------|
| CPU access | Software reads/writes peripherals | Correct behavior |
| DMA access | DMA transfers via crossbar | Data integrity |
| Mixed traffic | CPU and DMA concurrent | No deadlock, fair access |

: Level 3 Integration Tests

## Verification Collateral

### Available Test Infrastructure

| Item | Location | Description |
|------|----------|-------------|
| CocoTB tests | `dv/tests/` | Python testbenches |
| Wave configs | `dv/tests/GTKW/` | GTKWave configurations |
| Coverage | (implicit) | Functional coverage |

: Test Infrastructure

### Running Verification

```bash
# Run all crossbar tests
cd projects/components/apb_xbar/dv/tests/
pytest test_apb_xbar_*.py -v

# Run specific variant
pytest test_apb_xbar_2to4.py -v

# Generate waveforms
pytest test_apb_xbar_2to4.py --vcd=debug.vcd

# View waveforms
gtkwave debug.vcd
```

## Known Limitations

### Not Tested

| Scenario | Reason | Recommendation |
|----------|--------|----------------|
| Slave timeout | Not implemented | Add external watchdog |
| >16 masters/slaves | Generator limit | Custom modification needed |
| Non-64KB regions | Not supported | Use multiple crossbars |

: Known Limitations

---

**End of Hardware Architecture Specification**

---

## Related Documentation

- **[APB Crossbar MAS](../apb_xbar_mas/apb_xbar_mas_index.md)** - Detailed implementation
- **[PRD.md](../../PRD.md)** - Product requirements
- **[README.md](../../README.md)** - Quick start guide
