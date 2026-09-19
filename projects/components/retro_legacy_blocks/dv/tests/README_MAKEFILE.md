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
make run-apb4_hpet      # HPET tests only
make run-apb4_pit_8254       # PIT 8254 tests only
make run-apb4_rtc       # RTC tests only
make run-apb4_pic_8259       # 8259 PIC tests only
make run-ioapic    # IOAPIC tests only
make run-all       # All tests
```

## Test Levels

The RLB tests support three test levels controlled by the `TEST_LEVEL` environment variable:

| Level | Purpose | Duration | Coverage |
|-------|---------|----------|----------|
| **gate** | Quick smoke tests | ~30s | Core functionality |
| **func** | Moderate coverage | ~90s | Common scenarios |
| **full** | Comprehensive | ~180s | Edge cases, stress |

## Common Usage Patterns

### Run Specific Block at Different Levels

```bash
# HPET examples
make run-apb4_hpet-gate         # Quick test
make run-apb4_hpet-func        # More thorough
make run-apb4_hpet-full          # Comprehensive

# PIT examples
make run-apb4_pit_8254-gate          # Quick test
make run-apb4_pit_8254-func         # More thorough
make run-apb4_pit_8254-full           # Comprehensive
```

### Run with Waveforms

Add `-waves` suffix to any target to enable VCD waveform generation:

```bash
make run-apb4_hpet-gate-waves       # HPET gate with VCD
make run-apb4_pit_8254-func-waves       # PIT func with VCD
make run-all-gate-waves        # All tests gate with VCD
```

Waveforms are saved to: `local_sim_build/test_*/dump.vcd`

### Run in Parallel

Add `-parallel` suffix to run tests in parallel (8 threads default):

```bash
make run-apb4_hpet-gate-parallel    # HPET gate, 8 threads
make run-all-func-parallel    # All tests func, 8 threads
```

**Note:** Parallel execution does NOT currently work with waveforms due to pytest-xdist limitations.

### Combined Modes

You can combine level, parallel, and waves:

```bash
make run-apb4_hpet-full-parallel         # Full test level, parallel
make run-apb4_rtc-gate-waves            # Gate level, with waveforms
make run-all-func-parallel        # All tests, func level, parallel
```

## All Test Blocks

| Target Prefix | Block | Description |
|---------------|-------|-------------|
| `run-apb4_hpet-*` | HPET | High Precision Event Timer |
| `run-apb4_pit_8254-*` | PIT 8254 | Programmable Interval Timer |
| `run-apb4_rtc-*` | RTC | Real-Time Clock |
| `run-apb4_pic_8259-*` | 8259 PIC | Programmable Interrupt Controller |
| `run-ioapic-*` | IOAPIC | I/O Advanced PIC |

## Combined Test Runs

Run all blocks together:

```bash
# All tests at BASIC level
make run-all-gate
make run-all-gate-waves
make run-all-gate-parallel

# All tests at MEDIUM level
make run-all-func
make run-all-func-waves
make run-all-func-parallel

# All tests at FULL level
make run-all-full
make run-all-full-waves
make run-all-full-parallel
```

## Utility Targets

```bash
# Collect tests (show what would run without running)
make collect-apb4_hpet
make collect-apb4_pit_8254
make collect-apb4_rtc
make collect-apb4_pic_8259
make collect-ioapic

# Clean artifacts
make clean          # Clean __pycache__, .pytest_cache
make clean-all      # Clean everything (VCD, logs, build)
```

## Examples

### Quick Smoke Test (Fastest)
```bash
make run-all-gate
# ~2-3 minutes for all blocks
```

### Development Testing (Balanced)
```bash
make run-apb4_hpet-func-waves     # Test HPET with debug info
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
make run-apb4_pic_8259-gate-waves

# Open waveform
gtkwave local_sim_build/test_apb4_pic_8259_*/dump.vcd &
```

## Environment Variables

The Makefile respects these environment variables:

| Variable | Purpose | Default |
|----------|---------|---------|
| `TEST_LEVEL` | Test thoroughness | `gate` |
| `WAVES` | Enable VCD generation | `0` (off) |
| `REPO_ROOT` | Repository root | **Required** |

You can override them:

```bash
# Manual override
TEST_LEVEL=func WAVES=1 make run-apb4_hpet

# But Makefile targets are easier:
make run-apb4_hpet-func-waves
```

## Parallel Execution Details

The Makefile uses pytest-xdist for parallel execution. It is now a four-line
leaf including `make/tests.mk` (TOOL-008), so these are no longer set here:

- **Threads:** derived per host -- `JOBS = min(nproc, MemTotalGB / GB_PER_WORKER)`,
  `GB_PER_WORKER ?= 2`. Run `make jobs` to see what your host resolves to.
- **Reruns:** 3 retries, 1 s delay (`PYTEST_RERUNS ?= --reruns 3 --reruns-delay 1`).

There is no `PYTEST_XDIST` variable in this Makefile to edit. Override on the
command line instead:

```bash
# Override on command line (NOT RECOMMENDED - use Makefile targets)
TEST_LEVEL=gate pytest test_apb4_hpet.py -v --tb=short -n 16
```

## Comparison with Stream Tests

The RLB Makefile follows the same pattern as stream tests but uses different test levels:

| RLB Tests | Stream Tests | Equivalent |
|-----------|--------------|------------|
| `gate` | `GATE` | Quick smoke test |
| `func` | `FUNC` | Functional test |
| `full` | `FULL` | Comprehensive test |

**Key Difference:** RLB blocks use TEST_LEVEL (gate/func/full) while stream uses TEST_LEVEL (GATE/FUNC/FULL).

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
make run-apb4_hpet-gate

# Or increase timeout in test file
```

### Waveforms not generated
```bash
# Ensure using -waves suffix
make run-apb4_hpet-gate-waves

# Check if WAVES env var is set
echo $WAVES  # Should be "1"
```

### "No tests collected"
```bash
# Check test discovery
make collect-apb4_hpet

# Verify pytest can find tests
pytest test_apb4_hpet.py --collect-only
```

## Integration with CI/CD

Recommended CI workflow:

```bash
# Stage 1: Quick smoke test (all blocks, gate)
make run-all-gate-parallel

# Stage 2: Func coverage (all blocks, func)
make run-all-func-parallel

# Stage 3: Full regression (nightly, all blocks, full)
make run-all-full-parallel
```

## Related Files

- [Main Makefile](file://Makefile) - This file
- [HPET Tests](file://test_apb4_hpet.py) - HPET test suite
- [PIT Tests](file://test_apb4_pit_8254.py) - PIT 8254 test suite
- [RTC Tests](file://test_apb4_rtc.py) - RTC test suite
- [PIC Tests](file://test_apb4_pic_8259.py) - 8259 PIC test suite
- [IOAPIC Tests](file://test_apb4_ioapic.py) - IOAPIC test suite

## Version History

- **v1.0** (2025-11-16) - Initial Makefile creation
  - Support for 5 test blocks (HPET, PIT, RTC, PIC, IOAPIC)
  - Three test levels (gate, func, full)
  - Waveform and parallel execution support
