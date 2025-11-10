# SMBUS Tests

**Status:** 📋 Planned - Structure Created

---

## Test Organization

Tests are organized in 3 levels:

### Basic Tests
- Register access (read/write)
- Core functionality enable/disable
- Simple operation verification
- Interrupt generation
- **Target:** 4-6 tests, 100% pass rate, <30s per test

### Medium Tests
- Mode switching
- Multi-feature interaction
- Configuration edge cases
- **Target:** 5-8 tests, 100% pass rate, 30-90s per test

### Full Tests
- Stress testing (all resources active)
- Clock domain crossing variants (if CDC supported)
- Corner cases and timing edge cases
- **Target:** 3-5 tests, ≥95% pass rate, 90+ seconds per test

## Test Files (To Be Created)

- `test_apb_smbus.py` - Main test runner
- `conftest.py` - Pytest configuration

## Testbench Classes

Testbench classes are located in:
`dv/tbclasses/smbus/`

- `smbus_tb.py` - Main testbench
- `smbus_tests_basic.py` - Basic test suite
- `smbus_tests_medium.py` - Medium test suite
- `smbus_tests_full.py` - Full test suite

## Running Tests

```bash
# Run all tests
pytest dv/tests/smbus/ -v

# Run basic tests only
pytest dv/tests/smbus/ -v -k "basic"

# With waveforms
WAVES=1 pytest dv/tests/smbus/ -v
```

---

**Last Updated:** 2025-10-29
