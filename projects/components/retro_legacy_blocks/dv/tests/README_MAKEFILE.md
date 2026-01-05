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

# RLB Tests Makefile Guide

## Quick Start

```bash
# Setup environment (required)
cd $REPO_ROOT
source env_python

# Navigate to test directory
cd projects/components/retro_legacy_blocks/dv/tests

# Show all available targets
make help

# Run quick tests (BASIC level, single-threaded)
make run-hpet      # HPET tests only
make run-pit       # PIT 8254 tests only
make run-rtc       # RTC tests only
make run-pic       # 8259 PIC tests only
make run-ioapic    # IOAPIC tests only
make run-all       # All tests
```

## Test Levels

The RLB tests support three test levels controlled by the `TEST_LEVEL` environment variable:

| Level | Purpose | Duration | Coverage |
|-------|---------|----------|----------|
| **basic** | Quick smoke tests | ~30s | Core functionality |
| **medium** | Moderate coverage | ~90s | Common scenarios |
| **full** | Comprehensive | ~180s | Edge cases, stress |

## Common Usage Patterns

### Run Specific Block at Different Levels

```bash
# HPET examples
make run-hpet-basic         # Quick test
make run-hpet-medium        # More thorough
make run-hpet-full          # Comprehensive

# PIT examples
make run-pit-basic          # Quick test
make run-pit-medium         # More thorough
make run-pit-full           # Comprehensive
```

### Run with Waveforms

Add `-waves` suffix to any target to enable VCD waveform generation:

```bash
make run-hpet-basic-waves       # HPET basic with VCD
make run-pit-medium-waves       # PIT medium with VCD
make run-all-basic-waves        # All tests basic with VCD
```

Waveforms are saved to: `local_sim_build/test_*/dump.vcd`

### Run in Parallel

Add `-parallel` suffix to run tests in parallel (8 threads default):

```bash
make run-hpet-basic-parallel    # HPET basic, 8 threads
make run-all-medium-parallel    # All tests medium, 8 threads
```

**Note:** Parallel execution does NOT currently work with waveforms due to pytest-xdist limitations.

### Combined Modes

You can combine level, parallel, and waves:

```bash
make run-hpet-full-parallel         # Full test level, parallel
make run-rtc-basic-waves            # Basic level, with waveforms
make run-all-medium-parallel        # All tests, medium level, parallel
```

## All Test Blocks

| Target Prefix | Block | Description |
|---------------|-------|-------------|
| `run-hpet-*` | HPET | High Precision Event Timer |
| `run-pit-*` | PIT 8254 | Programmable Interval Timer |
| `run-rtc-*` | RTC | Real-Time Clock |
| `run-pic-*` | 8259 PIC | Programmable Interrupt Controller |
| `run-ioapic-*` | IOAPIC | I/O Advanced PIC |

## Combined Test Runs

Run all blocks together:

```bash
# All tests at BASIC level
make run-all-basic
make run-all-basic-waves
make run-all-basic-parallel

# All tests at MEDIUM level
make run-all-medium
make run-all-medium-waves
make run-all-medium-parallel

# All tests at FULL level
make run-all-full
make run-all-full-waves
make run-all-full-parallel
```

## Utility Targets

```bash
# Collect tests (show what would run without running)
make collect-hpet
make collect-pit
make collect-rtc
make collect-pic
make collect-ioapic

# Clean artifacts
make clean          # Clean __pycache__, .pytest_cache
make clean-all      # Clean everything (VCD, logs, build)
```

## Examples

### Quick Smoke Test (Fastest)
```bash
make run-all-basic
# ~2-3 minutes for all blocks
```

### Development Testing (Balanced)
```bash
make run-hpet-medium-waves     # Test HPET with debug info
# ~1-2 minutes, VCD available for debugging
```

### Full Regression (Comprehensive)
```bash
make run-all-full-parallel
# ~5-10 minutes for all blocks, parallel execution
```

### Debug Specific Issue
```bash
# Run single block at BASIC level with waveforms
make run-pic-basic-waves

# Open waveform
gtkwave local_sim_build/test_apb_pic_8259_*/dump.vcd &
```

## Environment Variables

The Makefile respects these environment variables:

| Variable | Purpose | Default |
|----------|---------|---------|
| `TEST_LEVEL` | Test thoroughness | `basic` |
| `WAVES` | Enable VCD generation | `0` (off) |
| `REPO_ROOT` | Repository root | **Required** |

You can override them:

```bash
# Manual override
TEST_LEVEL=medium WAVES=1 make run-hpet

# But Makefile targets are easier:
make run-hpet-medium-waves
```

## Parallel Execution Details

The Makefile uses pytest-xdist for parallel execution:

- **Default threads:** 8 (via `PYTEST_XDIST = -n 8`)
- **Reruns:** 0 retries on failure (via `PYTEST_RERUNS = --reruns 0`)

To change thread count, edit the Makefile `PYTEST_XDIST` variable or override:

```bash
# Override on command line (NOT RECOMMENDED - use Makefile targets)
TEST_LEVEL=basic pytest test_apb_hpet.py -v --tb=short -n 16
```

## Comparison with Stream Tests

The RLB Makefile follows the same pattern as stream tests but uses different test levels:

| RLB Tests | Stream Tests | Equivalent |
|-----------|--------------|------------|
| `basic` | `GATE` | Quick smoke test |
| `medium` | `FUNC` | Functional test |
| `full` | `FULL` | Comprehensive test |

**Key Difference:** RLB blocks use TEST_LEVEL (basic/medium/full) while stream uses TEST_LEVEL (GATE/FUNC/FULL).

## Troubleshooting

### Error: "REPO_ROOT is not set"
```bash
# Solution: Source env_python first
cd $REPO_ROOT
source env_python
```

### Tests hang or timeout
```bash
# Try without parallel execution
make run-hpet-basic

# Or increase timeout in test file
```

### Waveforms not generated
```bash
# Ensure using -waves suffix
make run-hpet-basic-waves

# Check if WAVES env var is set
echo $WAVES  # Should be "1"
```

### "No tests collected"
```bash
# Check test discovery
make collect-hpet

# Verify pytest can find tests
pytest test_apb_hpet.py --collect-only
```

## Integration with CI/CD

Recommended CI workflow:

```bash
# Stage 1: Quick smoke test (all blocks, basic)
make run-all-basic-parallel

# Stage 2: Medium coverage (all blocks, medium)
make run-all-medium-parallel

# Stage 3: Full regression (nightly, all blocks, full)
make run-all-full-parallel
```

## Related Files

- [Main Makefile](file://Makefile) - This file
- [HPET Tests](file://test_apb_hpet.py) - HPET test suite
- [PIT Tests](file://test_apb_pit_8254.py) - PIT 8254 test suite
- [RTC Tests](file://test_apb_rtc.py) - RTC test suite
- [PIC Tests](file://test_apb_pic_8259.py) - 8259 PIC test suite
- [IOAPIC Tests](file://test_apb_ioapic.py) - IOAPIC test suite

## Version History

- **v1.0** (2025-11-16) - Initial Makefile creation
  - Support for 5 test blocks (HPET, PIT, RTC, PIC, IOAPIC)
  - Three test levels (basic, medium, full)
  - Waveform and parallel execution support
