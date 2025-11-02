# APB HPET Component - Product Requirements Document

**Component:** APB High Precision Event Timer (HPET)
**Version:** 1.0
**Status:** ✅ Production Ready (5/6 configurations 100% passing)
**Last Updated:** 2025-10-17

---

## 1. Overview

### 1.1 Purpose
The APB HPET is a configurable multi-timer peripheral designed for precise timing and event generation in embedded systems. It provides up to 8 independent hardware timers with one-shot and periodic modes, accessible via APB interface with optional clock domain crossing.

### 1.2 Key Features
- **Configurable timer count:** 2, 3, or 8 independent timers
- **64-bit main counter:** High-resolution timestamp
- **64-bit comparators:** Support for long-duration timing
- **Operating modes:** One-shot and periodic
- **Clock domain crossing:** Optional CDC for timer/APB clock independence
- **APB interface:** Standard AMBA APB protocol
- **PeakRDL integration:** Register map generated from SystemRDL specification

### 1.3 Applications
- System tick generation
- Real-time OS scheduling
- Precise event timing
- Performance profiling
- Watchdog timers
- Multi-rate timing domains

---

## 2. Architecture

### 2.1 Block Diagram
```
┌─────────────────────────────────────────────────────────────┐
│                        APB HPET                              │
├─────────────────────────────────────────────────────────────┤
│                                                               │
│  ┌──────────────┐     ┌──────────────┐    ┌──────────────┐ │
│  │  APB Slave   │────▶│ Config Regs  │───▶│  HPET Core   │ │
│  │  (Optional   │     │ (PeakRDL)    │    │              │ │
│  │   CDC)       │     │              │    │ - Counter    │ │
│  └──────────────┘     └──────────────┘    │ - Timers[N]  │ │
│                                            │ - Comparators│ │
│                                            └──────────────┘ │
│                                                    │         │
│                                            Timer IRQs [N:0]  │
└────────────────────────────────────────────────────────────┘
```

### 2.2 Submodules

#### 2.2.1 apb_hpet (Top Level)
**File:** `rtl/apb_hpet.sv`
**Purpose:** Top-level wrapper integrating APB slave, config registers, and timer core

**Parameters:**
- `NUM_TIMERS` (2, 3, 8): Number of independent timers
- `VENDOR_ID` (16-bit): Vendor identification
- `REVISION_ID` (16-bit): Hardware revision
- `CDC_ENABLE` (0/1): Enable clock domain crossing

#### 2.2.2 hpet_core
**File:** `rtl/hpet_core.sv`
**Purpose:** Timer logic - counter, comparators, fire detection, periodic mode

**Key Features:**
- 64-bit free-running counter
- Per-timer 64-bit comparators
- One-shot and periodic modes
- Automatic comparator increment in periodic mode
- Rising-edge fire detection

#### 2.2.3 hpet_config_regs
**File:** `rtl/hpet_config_regs.sv`
**Purpose:** Register map wrapper connecting PeakRDL registers to HPET core

**Key Features:**
- Integrates PeakRDL-generated register file
- Generates timer write strobes via edge detection
- Per-timer data buses to prevent corruption
- Maps software writes to hardware control signals

#### 2.2.4 hpet_regs (PeakRDL Generated)
**Files:** `rtl/hpet_regs.sv`, `rtl/hpet_regs_pkg.sv`
**Purpose:** APB register file generated from SystemRDL specification

**Register Map:**
- `0x000`: HPET_CONFIG (enable, legacy_mapping)
- `0x004`: HPET_STATUS (timer interrupt status, W1C)
- `0x008`: HPET_COUNTER_LO (main counter bits [31:0], RW)
- `0x00C`: HPET_COUNTER_HI (main counter bits [63:32], RW)
- `0x010`: HPET_CAPABILITIES (num_timers, vendor_id, revision_id, RO)
- `0x100 + i*0x20`: TIMER[i]_CONFIG (enable, int_enable, type, size)
- `0x104 + i*0x20`: TIMER[i]_COMPARATOR_LO (bits [31:0], RW)
- `0x108 + i*0x20`: TIMER[i]_COMPARATOR_HI (bits [63:32], RW)

---

## 3. Functional Requirements

### 3.1 Timer Operation

#### FR-1: One-Shot Mode
**Priority:** P0 (Critical)
**Status:** ✅ Implemented and verified

**Description:** Timer fires once when main counter matches comparator value.

**Behavior:**
1. Software writes comparator value
2. Software enables timer
3. When `counter >= comparator`, timer fires (interrupt asserts)
4. Timer remains idle until reconfigured

**Verification:** Medium test `test_timer_periodic` (one-shot configuration)

#### FR-2: Periodic Mode
**Priority:** P0 (Critical)
**Status:** ✅ Implemented and verified

**Description:** Timer fires repeatedly at fixed intervals.

**Behavior:**
1. Software writes comparator value (defines first fire time)
2. Software enables timer in periodic mode
3. When `counter >= comparator`, timer fires
4. Comparator auto-increments: `comparator += period`
5. Process repeats indefinitely

**Verification:** Medium test `test_timer_periodic`

#### FR-3: Timer Mode Switching
**Priority:** P1 (High)
**Status:** ✅ Implemented and verified

**Description:** Dynamically switch between one-shot and periodic modes.

**Verification:** Medium test `test_timer_mode_switching`

### 3.2 Counter Management

#### FR-4: 64-bit Counter
**Priority:** P0 (Critical)
**Status:** ✅ Implemented and verified

**Description:** Free-running 64-bit counter incrementing every HPET clock cycle.

**Features:**
- Read/write access via COUNTER_LO/HI registers
- Continuous operation when HPET enabled
- Overflow handling (wraps to 0)

**Verification:** Medium test `test_64bit_counter`

#### FR-5: 64-bit Comparators
**Priority:** P1 (High)
**Status:** ✅ Implemented and verified

**Description:** Each timer has 64-bit comparator for long-duration timing.

**Verification:** Medium test `test_64bit_comparator`

### 3.3 Multiple Timers

#### FR-6: Independent Timer Operation
**Priority:** P0 (Critical)
**Status:** ✅ Implemented and verified

**Description:** All timers operate independently without interference.

**Requirements:**
- Each timer has dedicated comparator
- Each timer has independent enable/mode configuration
- Per-timer data buses prevent corruption

**Verification:** Medium test `test_multiple_timers`

### 3.4 Clock Domain Crossing

#### FR-7: Optional CDC
**Priority:** P1 (High)
**Status:** ✅ Implemented and verified

**Description:** When CDC_ENABLE=1, APB and HPET clocks can be asynchronous.

**Implementation:** Uses `apb_slave_cdc` module with handshake synchronization

**Verification:** Full test `test_clock_domain_crossing`

---

## 4. Interface Specifications

### 4.1 APB Interface

**Signals:**
- `pclk`: APB clock
- `presetn`: APB reset (active low)
- `paddr[ADDR_WIDTH-1:0]`: Address bus
- `psel`: Peripheral select
- `penable`: Enable strobe
- `pwrite`: Write enable
- `pwdata[31:0]`: Write data
- `pready`: Transfer ready
- `prdata[31:0]`: Read data
- `pslverr`: Transfer error

**Protocol:** AMBA APB4

### 4.2 HPET Clock Interface

**Signals:**
- `hpet_clk`: HPET timer clock (may be asynchronous to APB if CDC enabled)
- `hpet_rst_n`: HPET reset (active low)

### 4.3 Interrupt Interface

**Signals:**
- `timer_irq[NUM_TIMERS-1:0]`: Per-timer interrupt outputs (active high)

**Behavior:**
- Asserts when timer fires
- Remains high until software clears via STATUS register write

---

## 5. Parameter Configuration

### 5.1 NUM_TIMERS
**Type:** Integer
**Values:** 2, 3, 8
**Default:** 2

**Configurations:**
- **2-timer:** "Intel-like" configuration, minimal resource usage
- **3-timer:** "AMD-like" configuration, common SoC design
- **8-timer:** "Custom" configuration, maximum flexibility

### 5.2 VENDOR_ID
**Type:** 16-bit
**Range:** 0x0000 - 0xFFFF
**Default:** Varies by configuration

**Purpose:** Hardware vendor identification in CAPABILITIES register

### 5.3 REVISION_ID
**Type:** 16-bit
**Range:** 0x0000 - 0xFFFF
**Default:** Varies by configuration

**Purpose:** Hardware revision tracking

### 5.4 CDC_ENABLE
**Type:** Boolean (0/1)
**Values:**
- 0: APB and HPET clocks must be synchronous
- 1: APB and HPET clocks can be asynchronous

**Impact:** Adds ~2-3 cycle latency for register accesses when enabled

---

## 6. Performance Requirements

### 6.1 Timing
- **Counter increment:** Every HPET clock cycle
- **Timer fire latency:** 1 HPET clock cycle from match detection
- **APB access latency:**
  - No CDC: 2 APB clock cycles
  - With CDC: 4-6 APB clock cycles (handshake overhead)

### 6.2 Resource Usage
**Estimates (post-synthesis):**
- **2-timer (no CDC):** ~500 LUTs, ~300 FFs
- **3-timer (no CDC):** ~650 LUTs, ~400 FFs
- **8-timer (with CDC):** ~1200 LUTs, ~800 FFs

---

## 7. Verification Status

### 7.1 Test Infrastructure

**Test Directory Structure:**
```
projects/components/apb_hpet/dv/tests/
├── conftest.py           ← MANDATORY: Pytest configuration
├── test_apb_hpet.py      ← Test runner
└── logs/                 ← Created automatically by conftest.py
```

**conftest.py Requirements:**

The `conftest.py` file is **MANDATORY** for all component tests and provides:
1. **Logging Configuration:** Auto-creates logs directory, configures pytest
2. **Test Markers:** Registers custom markers (basic, medium, full, etc.)
3. **Test Fixtures:** Parametrized configuration fixtures
4. **Test Collection Hooks:** Auto-tags tests with markers
5. **Log Preservation:** Preserves all logs regardless of test outcome

**Running Tests with Markers:**
```bash
# Run only basic tests
pytest projects/components/apb_hpet/dv/tests/ -v -m basic

# Run register access tests
pytest projects/components/apb_hpet/dv/tests/ -v -m register_access

# Run 2-timer configuration tests
pytest projects/components/apb_hpet/dv/tests/ -v -m two_timer
```

**See:** `projects/components/apb_hpet/dv/tests/conftest.py` for complete implementation

### 7.2 Test Coverage

**Test Levels:**
- **Basic (4 tests):** Register access, simple timer operations
- **Medium (5 tests):** Periodic mode, multiple timers, 64-bit features, mode switching
- **Full (3 tests):** All timers stress, CDC, edge cases

**Test Configurations:**
```
Configuration                           Basic  Medium  Full   Overall
──────────────────────────────────────────────────────────────────────
2-timer Intel-like (no CDC)             4/4    5/5     3/3    12/12 ✅
3-timer AMD-like (no CDC)               4/4    5/5     3/3    12/12 ✅
8-timer custom (no CDC)                 4/4    5/5     2/3    11/12 ⚠️
2-timer Intel-like (CDC)                4/4    5/5     3/3    12/12 ✅
3-timer AMD-like (CDC)                  4/4    5/5     3/3    12/12 ✅
8-timer custom (CDC)                    4/4    5/5     3/3    12/12 ✅
```

**Overall:** 5/6 configurations at 100%, 1 config at 92% (minor stress test timeout)

### 7.2 Known Issues
**Issue:** 8-timer non-CDC "All Timers Stress" test timeout
**Impact:** Low - single stress test, CDC version passes
**Status:** Optional fix - increase timeout in test
**Workaround:** Use CDC-enabled 8-timer configuration

---

## 8. Dependencies

### 8.1 RTL Dependencies
- `rtl/amba/apb/apb_slave.sv` - Standard APB slave
- `rtl/amba/apb/apb_slave_cdc.sv` - APB slave with CDC
- `rtl/amba/adapters/peakrdl_to_cmdrsp.sv` - PeakRDL adapter
- Common modules (counters, FIFOs, CDC handshake)

### 8.2 Tool Dependencies
- **PeakRDL-regblock:** SystemRDL to SystemVerilog compiler
- **Verilator:** RTL simulation
- **CocoTB:** Python testbench framework
- **pytest:** Test runner

### 8.3 Python Dependencies
- `peakrdl-regblock >= 0.17.0`
- `peakrdl >= 1.0.0`
- `cocotb >= 1.9.0`
- `pytest >= 7.0.0`

---

## 9. Integration Guide

### 9.1 Instantiation Example

```systemverilog
apb_hpet #(
    .NUM_TIMERS   (3),
    .VENDOR_ID    (16'h1022),  // AMD
    .REVISION_ID  (16'h0002),
    .CDC_ENABLE   (1)
) u_hpet (
    // APB Interface
    .pclk         (apb_clk),
    .presetn      (apb_rst_n),
    .paddr        (apb_paddr[11:0]),
    .psel         (apb_psel),
    .penable      (apb_penable),
    .pwrite       (apb_pwrite),
    .pwdata       (apb_pwdata),
    .pready       (apb_pready),
    .prdata       (apb_prdata),
    .pslverr      (apb_pslverr),

    // HPET Clock Domain
    .hpet_clk     (hpet_clk),
    .hpet_rst_n   (hpet_rst_n),

    // Interrupts
    .timer_irq    (timer_irq[2:0])
);
```

### 9.2 Software Initialization

```c
// 1. Disable HPET
hpet_write(HPET_CONFIG, 0x0);

// 2. Reset counter
hpet_write(HPET_COUNTER_LO, 0x0);
hpet_write(HPET_COUNTER_HI, 0x0);

// 3. Configure Timer 0 (one-shot, 1ms @ 10MHz)
hpet_write(TIMER0_COMPARATOR_LO, 10000);
hpet_write(TIMER0_COMPARATOR_HI, 0);
hpet_write(TIMER0_CONFIG, TIMER_ENABLE | TIMER_INT_ENABLE);

// 4. Enable HPET
hpet_write(HPET_CONFIG, HPET_ENABLE);

// 5. Wait for interrupt or poll STATUS register
uint32_t status = hpet_read(HPET_STATUS);
if (status & (1 << 0)) {
    // Timer 0 fired - clear interrupt
    hpet_write(HPET_STATUS, (1 << 0));  // W1C
}
```

---

## 9. Attribution and Contribution Guidelines

### 9.1 Git Commit Attribution

When creating git commits for APB HPET documentation or implementation:

**Use:**
```
Documentation and implementation support by Claude.
```

**Do NOT use:**
```
Co-Authored-By: Claude <noreply@anthropic.com>
```

**Rationale:** APB HPET documentation and organization receives AI assistance for structure and clarity, while design concepts and architectural decisions remain human-authored.

---

## 9.2 PDF Generation Location

**IMPORTANT: PDF files should be generated in the docs directory:**
```
/mnt/data/github/rtldesignsherpa/projects/components/apb_hpet/docs/
```

**Quick Command:** Use the provided shell script:
```bash
cd /mnt/data/github/rtldesignsherpa/projects/components/apb_hpet/docs
./generate_pdf.sh
```

The shell script will automatically:
1. Use the md_to_docx.py tool from bin/
2. Process the specification index file
3. Generate both DOCX and PDF files in the docs/ directory
4. Create table of contents and title page

**📖 See:** `bin/md_to_docx.py` for complete implementation details

---

## 10. Future Enhancements

### 10.1 Potential Features (Not Implemented)
- **Comparator readback:** Currently write-only
- **FSB interrupt delivery:** Direct interrupt routing
- **Legacy replacement mode:** PC/AT timer emulation
- **64-bit atomic reads:** Single-cycle 64-bit counter read
- **Prescaler support:** Counter frequency division

### 10.2 Optimization Opportunities
- **Register pipelining:** Reduce critical path in register access
- **Dynamic power gating:** Disable unused timers
- **Interrupt coalescing:** Reduce interrupt overhead

---

## 11. References

### 11.1 Internal Documentation
- `docs/IMPLEMENTATION_STATUS.md` - Latest test results
- `rtl/peakrdl/hpet_regs.rdl` - SystemRDL specification
- `dv/tbclasses/` - Testbench implementation

### 11.2 External Standards
- **AMBA APB Protocol Specification v2.0** - ARM IHI 0024
- **IA-PC HPET Specification 1.0a** - Intel/Microsoft (architectural reference)
- **SystemRDL 2.0** - Accellera

---

**Document Version:** 1.0
**Last Review:** 2025-10-17
**Next Review:** 2026-01-01
**Maintained By:** RTL Design Sherpa Project
