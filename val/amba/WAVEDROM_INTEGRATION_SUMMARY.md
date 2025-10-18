# AMBA WaveDrom Integration Summary

**Date:** 2025-10-06
**Status:** ✅ COMPLETE (GAXI + APB)

## Overview

Added WaveDrom timing diagram generation to GAXI and APB protocol tests. When enabled, these tests generate WaveJSON files showing protocol behavior across different scenarios.

**Protocols Integrated:**
- ✅ GAXI (sync and async buffers)
- ✅ APB (master, slave, slave CDC)

## Files Modified

---

## GAXI Protocol Integration

### 1. test_gaxi_buffer_sync.py
**Changes:**
- Added WaveDrom imports (lines 28-46)
- Added `gaxi_wavedrom_test()` cocotb function (lines 163-361)
- Added `test_gaxi_buffer_wavedrom()` pytest test (lines 540-682)

**Generates:**
- 9 WaveJSON files (3 modes × 3 scenarios each)
- Modes: skid, fifo_mux, fifo_flop
- Scenarios per mode:
  1. Write to empty (shows bypass/latency)
  2. Burst write until full (backpressure)
  3. Simultaneous read/write (pass-through)

### 2. test_gaxi_buffer_async.py
**Changes:**
- Added WaveDrom imports (lines 28-47)
- Added `gaxi_async_wavedrom_test()` cocotb function (lines 200-410)
- Added `test_gaxi_buffer_async_wavedrom()` pytest test (lines 413-572)

**Generates:**
- 9 WaveJSON files (3 modes × 3 scenarios each)
- Modes: skid, fifo_mux, fifo_flop
- Clock ratio: 10ns:12ns (1.2x, demonstrates CDC)
- Scenarios per mode:
  1. Write to empty (shows CDC latency)
  2. Backpressure with CDC
  3. Continuous flow across CDC

---

## APB Protocol Integration

### 3. test_apb_master.py
**Changes:**
- Added WaveDrom imports (lines 26-35)
- Added `apb_master_wavedrom_test()` cocotb function (lines 793-955)
- Added `test_apb_master_wavedrom()` pytest test (lines 1154-1249)

**Generates:**
- 3 WaveJSON files showing APB master perspective:
  1. Basic write with wait state
  2. Basic read with data return
  3. Back-to-back transactions (write then read)

**Signals:** APB master signals (m_apb_*)

### 4. test_apb_slave.py
**Changes:**
- Added WaveDrom imports (lines 28-37)
- Added `apb_slave_wavedrom_test()` cocotb function (lines 964-1111)
- Added `test_apb_slave_wavedrom()` pytest test (lines 1262-1355)

**Generates:**
- 3 WaveJSON files showing APB slave perspective:
  1. Write with wait states (slave generates wait states)
  2. Read with immediate response (slave responds quickly)
  3. Back-to-back transactions (slave handles sequential operations)

**Signals:** APB slave signals (s_apb_*)

### 5. test_apb_slave_cdc.py
**Changes:**
- Added WaveDrom imports (lines 28-37)
- Added `apb_slave_cdc_wavedrom_test()` cocotb function (lines 979-1162)
- Added `test_apb_slave_cdc_wavedrom()` pytest test (lines 1320-1418)

**Generates:**
- 3 WaveJSON files showing CDC behavior with BOTH APB and GAXI interfaces:
  1. Write CDC (APB domain → GAXI domain)
  2. Read CDC (GAXI response → APB domain)
  3. Back-to-back CDC transactions

**Signals:**
- APB slave signals (s_apb_*) @ pclk domain
- GAXI CMD signals (gaxi_cmd_*) @ aclk domain
- GAXI RSP signals (gaxi_rsp_*) @ aclk domain

**Special Features:**
- Dual clock groups showing async operation
- CDC timing relationships visible
- Cross-domain signal flow

---

## Running the Tests

### GAXI Tests

#### Run all GAXI WaveDrom tests:
```bash
pytest test_gaxi_buffer_sync.py::test_gaxi_buffer_wavedrom -v
pytest test_gaxi_buffer_async.py::test_gaxi_buffer_async_wavedrom -v
```

#### Run original GAXI functional tests (no WaveDrom):
```bash
pytest test_gaxi_buffer_sync.py::test_gaxi_buffer_sync -v
pytest test_gaxi_buffer_async.py::test_gaxi_buffer_async -v
```

### APB Tests

#### Run all APB WaveDrom tests:
```bash
ENABLE_WAVEDROM=1 pytest test_apb_master.py::test_apb_master_wavedrom -v
ENABLE_WAVEDROM=1 pytest test_apb_slave.py::test_apb_slave_wavedrom -v
ENABLE_WAVEDROM=1 pytest test_apb_slave_cdc.py::test_apb_slave_cdc_wavedrom -v
```

#### Run original APB functional tests (no WaveDrom):
```bash
pytest test_apb_master.py::test_apb_master -v
pytest test_apb_slave.py::test_apb_gaxi_refactor_debug -v
pytest test_apb_slave_cdc.py::test_comprehensive_apb_cdc -v
```

## Design Decisions

1. **Separate tests:** WaveDrom tests are separate from functional tests
   - Keeps functional tests fast and focused
   - WaveDrom tests are opt-in via specific test names

2. **ENABLE_WAVEDROM flag:** Set to 1 in wavedrom tests, 0 by default
   - Prevents accidental waveform generation in functional tests
   - Explicit control over when diagrams are created

3. **Focused scenarios:** 3 scenarios per mode (not 6 like example)
   - Reduced complexity while covering key behaviors
   - Faster test execution

4. **Segmented capture:** Using start/stop/solve/clear pattern
   - Prevents spurious constraint matches across scenarios
   - Clean, isolated waveforms per scenario

5. **Auto-binding:** Protocol-aware signal discovery
   - Automatically finds wr_*/rd_* signals
   - Consistent field formatting (hex for data, decimal for count)

## Output Structure

```
val/amba/
├── WaveJSON/
│   ├── GAXI (18 files total):
│   │   ├── test_gaxi_sync_skid_*.json (3 files)
│   │   ├── test_gaxi_sync_fifo_mux_*.json (3 files)
│   │   ├── test_gaxi_sync_fifo_flop_*.json (3 files)
│   │   ├── test_gaxi_async_skid_*.json (3 files)
│   │   ├── test_gaxi_async_fifo_mux_*.json (3 files)
│   │   └── test_gaxi_async_fifo_flop_*.json (3 files)
│   └── APB (9 files total):
│       ├── test_apb_master_*.json (3 files)
│       ├── test_apb_slave_*.json (3 files)
│       └── test_apb_slave_cdc_*.json (3 files)
├── PNG/ (generated from WaveJSON via wavedrom-cli)
└── SVG/ (generated from WaveJSON via wavedrom-cli)
```

**Total WaveJSON outputs:** 27 files (18 GAXI + 9 APB)

## Key Features

### GAXI Sync Tests
- Single clock domain (10ns period)
- Shows zero-latency bypass (skid mode)
- Shows 1-cycle latency (fifo_mux mode)
- Shows 2-cycle latency (fifo_flop mode)
- Labeled groups: ["Write", wr_signals...], ["Read", rd_signals...], ["Internal", count...]

### GAXI Async Tests
- Dual clock domains (wr=10ns, rd=12ns)
- Shows CDC latency (3-5 cycles typical)
- Shows clock domain crossing with curved arrows (~>)
- Labeled groups: ["Clocks", clk_signals...], ["Write", wr_signals...], ["Read", rd_signals...], ["Internal", count...]

### APB Master Tests
- Single clock domain (pclk=10ns)
- Shows master perspective (initiating transactions)
- APB signals: psel, penable, pready, pwrite, paddr, pwdata, prdata
- Scenarios: write with wait, read, back-to-back

### APB Slave Tests
- Single clock domain (pclk=10ns)
- Shows slave perspective (responding to transactions)
- APB signals: Same as master, but slave-driven pready
- Scenarios: write with wait states, read immediate, back-to-back

### APB Slave CDC Tests
- **Dual clock domains:** pclk=10ns (APB), aclk=2ns (GAXI)
- **Dual protocol interfaces:** APB + GAXI (CMD/RSP)
- Shows clock domain crossing between APB and GAXI
- Demonstrates async FIFO behavior
- Scenarios: write CDC, read CDC, back-to-back CDC

## Technical Details

### Constraint Solver Usage
- Uses TemporalConstraintSolver from CocoTBFramework
- Protocol-aware pattern matching for GAXI handshakes
- Supports temporal relations: BEFORE, AFTER, SAME_CYCLE, WITHIN
- Automatic signal transition detection

### Field Configuration

**GAXI:**
- Uses `get_gaxi_field_config()` for protocol-specific formatting
- Data fields: 8-bit hex (0xC0)
- Count fields: 4-bit decimal (2, 3, 4)
- Proper field definitions attached to SignalConfig

**APB:**
- Uses `get_apb_field_config()` for protocol-specific formatting
- Address fields: 32-bit hex (0x00001000)
- Data fields: 32-bit hex (0xDEADBEEF)
- Control signals: Binary (1-bit)

### Edge Annotations
- Sync tests: Straight arrows (->) for same-cycle/sequential relationships
- Async tests: Curved arrows (~>) for CDC paths
- Shows data flow and timing relationships

## Documentation

See also:
- `docs/markdown/RTLAmba/gaxi/index.md` - GAXI overview
- `docs/markdown/RTLAmba/gaxi/gaxi_skid_buffer.md` - Embedded waveform examples
- `bin/CocoTBFramework/tbclasses/wavedrom_user/WAVEDROM_REQUIREMENTS.md` - WaveDrom framework docs

## Version History

- **2025-10-06 (Evening):** APB protocol integration complete
  - APB master: ✅ Complete (3 scenarios)
  - APB slave: ✅ Complete (3 scenarios)
  - APB slave CDC: ✅ Complete (3 scenarios, dual protocols)
  - Documentation: ✅ Updated
  - Total APB WaveJSON outputs: 9 files

- **2025-10-06 (Morning):** GAXI protocol integration complete
  - Sync test: ✅ Complete (9 scenarios)
  - Async test: ✅ Complete (9 scenarios)
  - Documentation: ✅ Complete
  - Total GAXI WaveJSON outputs: 18 files

**Overall Status:**
- Protocols integrated: GAXI + APB ✅
- Total WaveJSON outputs: 27 files
- Test files modified: 5
- Pattern established for future protocol integrations
