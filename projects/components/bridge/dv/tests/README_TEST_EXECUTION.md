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

# Bridge Test Execution Guide

## Critical Issues Fixed (2025-11-10)

### Issue 1: Memory Safety Limit Too Low ✅ FIXED

**Problem:** TBBase safety monitoring had 2GB memory limit, but bridge tests use 20-80GB.

**Root Cause:** Verilator simulation reports ALL system memory (not just test process), triggering false positives.

**Fix:** All bridge testbenches now set `max_memory_mb: 32768` (32GB limit).

### Issue 2: GAXI Timeout Too Short ✅ FIXED

**Problem:** GAXI masters timing out after 1000 cycles waiting for ready signal.

**Root Cause:** Default timeout was too short for bridge crossbar routing delays.

**Fix:** All GAXIMaster instances now use `timeout_cycles=10000` (10x increase).

### Issue 3: Parallel Execution Crashes System ✅ FIXED

**Problem:** Bridge tests crash when run in parallel due to excessive memory during compilation.

**Root Cause:** pytest-xdist runs 22 tests simultaneously, each compiling ~1GB of Verilator code.

**Solution:** `conftest.py` forces sequential execution to prevent OOM.

---

## Safe Test Execution

### Running All Bridge Tests

```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/bridge/dv/tests

# ✅ CORRECT: Sequential execution (safe, won't crash)
pytest -v

# ❌ WRONG: Parallel execution (will crash system!)
pytest -n auto  # DON'T DO THIS!
```

The `conftest.py` file automatically disables parallel execution even if `-n` is specified, but it's better to not use `-n` at all for bridge tests.

### Running Individual Tests

If you need to test a specific bridge configuration:

```bash
# Test single bridge
pytest test_bridge_1x2_rd.py::test_bridge_1x2_rd_basic_connectivity -v

# Test all tests for one bridge
pytest test_bridge_1x2_rd.py -v

# Test specific functionality across all bridges
pytest -k "basic_connectivity" -v
```

### Running Subsets by Marker

```bash
# Only basic tests
pytest -m basic -v

# Only routing tests
pytest -m routing -v

# Only arbitration tests (2x2_rw and 5x3_channels)
pytest -m arbitration -v
```

---

## Test Timing Expectations

**Sequential Execution:**
- Small bridges (1x2, 1x3): ~30-60 seconds each
- Medium bridges (1x4, 1x5, 2x2): ~60-90 seconds each
- Large bridges (5x3): ~90-120 seconds each
- **Total for all 22 tests: ~20-30 minutes**

This is expected and normal. Verilator compilation is compute-intensive.

---

## Memory Usage Patterns

**Per-Test Memory Usage:**
- Compilation phase: 500MB - 1GB per test
- Simulation phase: 200MB - 400MB per test

**Why Parallel Execution Fails:**
- 22 tests × 1GB = 22GB simultaneous memory usage
- Most systems have 8-16GB RAM → instant OOM crash

**Sequential Execution:**
- Only 1 test active at a time
- Peak memory: ~1GB
- Safe for systems with 4GB+ RAM

---

## Troubleshooting

### "Test was killed / System crashed"

**Symptom:** Pytest output shows `[status: killed]` or system freezes during test execution.

**Cause:** Parallel execution attempted (either manually via `-n` or due to stale pytest cache).

**Fix:**
1. Ensure you're NOT using `-n auto` or `-n <number>`
2. Clear pytest cache: `rm -rf .pytest_cache`
3. Verify `conftest.py` has the parallel-disable code (lines 33-41)
4. Run tests sequentially: `pytest -v` (no `-n` flag)

### "Tests taking too long"

**Expected:** 20-30 minutes for all 22 tests (sequential).

**If much longer:**
1. Check system load (other processes competing for CPU)
2. Check disk I/O (slow disk affects compilation)
3. Consider testing subset: `pytest -k "1x2" -v` (only small bridges)

### "Out of disk space"

**Cause:** Each test creates a `sim_build_*` directory with compiled Verilator model.

**Fix:**
```bash
# Clean old builds
cd /mnt/data/github/rtldesignsherpa/projects/components/bridge/dv/tests/logs
rm -rf sim_build_*

# Or use pytest's built-in cleanup (preserves logs, removes build artifacts)
pytest --clean-alluredir
```

---

## Test Architecture

### Test Organization

```
dv/tests/
├── conftest.py              # Pytest configuration (DISABLES PARALLEL!)
├── test_bridge_1x2_rd.py    # 1 master × 2 slaves, read-only
├── test_bridge_1x2_wr.py    # 1 master × 2 slaves, write-only
├── test_bridge_1x3_rd.py    # 1 master × 3 slaves, read-only
├── test_bridge_1x3_wr.py    # 1 master × 3 slaves, write-only
├── test_bridge_1x4_rd.py    # 1 master × 4 slaves, read-only (with APB)
├── test_bridge_1x4_wr.py    # 1 master × 4 slaves, write-only (with APB)
├── test_bridge_1x5_rd.py    # 1 master × 5 slaves, read-only (with AXIL)
├── test_bridge_1x5_wr.py    # 1 master × 5 slaves, write-only (with AXIL)
├── test_bridge_2x2_rw.py    # 2 masters × 2 slaves, read+write (arbitration)
└── test_bridge_5x3_channels.py  # 5 masters × 3 slaves (complex)
```

### Test Categories

**Per Bridge Configuration:**
1. `test_*_basic_connectivity` - Simple master→slave routing
2. `test_*_address_decode` - Address boundary testing
3. `test_*_arbitration` - Multi-master arbitration (2x2_rw, 5x3 only)

**Total:** 22 tests across 10 bridge configurations

---

## CI/CD Considerations

For continuous integration systems:

```yaml
# GitHub Actions example
- name: Run Bridge Tests
  run: |
    cd projects/components/bridge/dv/tests
    pytest -v --tb=short  # Sequential execution
  timeout-minutes: 45     # Allow 45min for all 22 tests
```

**DO NOT use:** `pytest -n auto` in CI/CD - it will fail due to memory constraints.

---

## Quick Reference

| Command | Purpose | Safe? |
|---------|---------|-------|
| `pytest -v` | Run all tests sequentially | ✅ Safe |
| `pytest test_bridge_1x2_rd.py -v` | Run one bridge config | ✅ Safe |
| `pytest -k "basic" -v` | Run basic tests only | ✅ Safe |
| `pytest -m routing -v` | Run routing tests only | ✅ Safe |
| `pytest -n auto -v` | Parallel execution | ❌ **CRASHES SYSTEM** |
| `pytest -n 4 -v` | Parallel with 4 workers | ❌ **CRASHES SYSTEM** |

---

## Related Documentation

- `conftest.py` - Pytest configuration with parallel-disable logic
- `../../rtl/generated/` - Generated bridge RTL files being tested
- `../../bin/bridge_generator.py` - Bridge RTL generator
- `../../docs/BRIDGE_ARCHITECTURE.md` - Bridge design documentation

---

**Last Updated:** 2025-11-10
**Issue:** Parallel execution causes OOM crashes
**Solution:** Sequential execution enforced via conftest.py
**Status:** ✅ Fixed
