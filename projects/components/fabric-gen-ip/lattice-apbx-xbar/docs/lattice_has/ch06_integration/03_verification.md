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

The Lattice is pre-verified:

| Test / Variant | Transactions | Status | Coverage |
|----------------|--------------|--------|----------|
| apbx_xbar_1to1 | 100+ | Pass | Basic connectivity |
| apbx_xbar_2to1 | 130+ | Pass | Arbitration stress |
| apbx_xbar_1to4 | 200+ | Pass | Address decode |
| apbx_xbar_2to4 | 350+ | Pass | Full crossbar stress |
| apbx_xbar_2to2_mixed | 8 directed | Pass | All four APB4/APB5 pairings, sideband gating, decode miss, structural pin check |
| apbx_xbar_timing | 2 variants | Pass | Published latency/cadence figures, both variant classes |

: Pre-Verification Status

**Overall:** 100% passing (9/9), >750 transactions plus the directed
mixed-version and timing checks. `apbx_xbar_2to2_mixed` also has a formal
harness (`formal/apbx_xbar/apbx_xbar_2to2_mixed/`).


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
- Invalid address behavior (decoding variants complete the access with PSLVERR; they do not hang -- see 4.1)

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

### APB5 Sideband Gating (mixed variant)

For `apbx_xbar_2to2_mixed`:
- All four APB4/APB5 master/slave pairings exercised
- Sideband signals flow only where both ends are APB5
- APB4 ports carry no sideband pins (structural check)
- Decode-miss completes with `PSLVERR`

### Timing and Protocol Compliance

`test_apbx_xbar_timing` asserts the published figures against the RTL:
- Single-transfer latency for single-master and arbitrated classes
- Back-to-back cadence (PREADY-to-PREADY)
- Forward-path and response-path breakdown
- Downstream setup-phase count (`[1,1,1,1,1]`)

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
| Coverage | `dv/tests/coverage_reports/` | Merged functional coverage reports |
| Build orchestration | `dv/tests/Makefile` | Area Makefile delegating to `make/tests.mk` |
| Formal harness (mixed variant) | `formal/apbx_xbar/apbx_xbar_2to2_mixed/` | Sideband-gating proofs |

: Test Infrastructure

### Running Verification

Tests are run through the area `Makefile` (which delegates to the shared
`make/tests.mk` infrastructure); bare `pytest` is not the supported entry
point because the Makefile supplies filelists, levels, and coverage
options.

```bash
cd projects/components/fabric-gen-ip/lattice-apbx-xbar/dv/tests/

# Run all crossbar tests -- clean-all first for a run you intend to trust
make clean-all && make run-all-gate

# Run specific variant
make run-apbx_xbar_2to4-gate

# Run with waveforms (WAVES=1 via the target)
make run-apbx_xbar_2to4-gate-waves
# create_view_cmd() writes the gtkwave command beside the log
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

- **[Lattice MAS](../../lattice_mas/lattice_mas_index.md)** - Detailed implementation
- **[PRD.md](../../../PRD.md)** - Product requirements
- **[README.md](../../../README.md)** - Quick start guide
