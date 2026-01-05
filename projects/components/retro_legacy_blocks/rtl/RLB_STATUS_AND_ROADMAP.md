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

# Retro Legacy Blocks (RLB) - Complete Status and Roadmap

**Date:** 2025-11-29
**Purpose:** Track completion status and remaining work for all RLB modules

---

## Module Implementation Status

### COMPLETE - With APB Wrappers

| Module | RTL Complete | APB Wrapper | PeakRDL | CDC Support | Validation | Status |
|--------|--------------|-------------|---------|-------------|------------|--------|
| **HPET** | Yes | apb_hpet.sv | Yes | CDC_ENABLE | Has tests | REFERENCE |
| **PIT_8254** | Yes | apb_pit_8254.sv | Yes | CDC_ENABLE | Has tests | COMPLETE |
| **RTC** | Yes | apb_rtc.sv | Yes | Yes | Has tests | COMPLETE |
| **PIC_8259** | Yes | apb_pic_8259.sv | Yes | Yes | Basic only | NEEDS TESTS |
| **SMBus** | Yes | apb_smbus.sv | Yes | CDC_ENABLE | None yet | NEEDS TESTS |
| **PM_ACPI** | Yes | apb_pm_acpi.sv | Yes | CDC_ENABLE | 6 tests | COMPLETE |
| **IOAPIC** | Yes | apb_ioapic.sv | Yes | CDC_ENABLE | None yet | NEEDS TESTS |
| **GPIO** | Yes | apb_gpio.sv | Yes | CDC_ENABLE | 6 tests | COMPLETE |

### COMPLETE - With APB Wrappers (cont.)

| Module | RTL Complete | APB Wrapper | PeakRDL | CDC Support | Validation | Status |
|--------|--------------|-------------|---------|-------------|------------|--------|
| **UART_16550** | Yes | apb_uart_16550.sv | Yes | CDC_ENABLE | TB Ready | PORT MISMATCH |

**CRITICAL NOTE (2025-11-30):**
GPIO and UART_16550 RTL modules have PORT NAME MISMATCHES with the actual
apb_slave.sv and peakrdl_to_cmdrsp.sv infrastructure modules.

**Issues:**
1. apb_slave.sv uses `s_apb_PSEL` naming, RTL uses `psel`
2. peakrdl_to_cmdrsp.sv uses `aclk`/`aresetn`, RTL uses `clk`/`rst_n`
3. CMD/RSP port naming differs (e.g., `cmd_addr` vs `cmd_paddr`)

**Resolution Required:**
Either update GPIO/UART_16550 wrappers to match infrastructure port names,
OR update infrastructure to provide consistent naming.

**Test Infrastructure Status:**
- UART 16550 testbench classes: COMPLETE (uart_16550_tb.py)
- UART 16550 test suites: COMPLETE (basic, medium, full)
- UART 16550 test runner: COMPLETE (test_apb_uart_16550.py)
- Tests use UART BFM from CocoTBFramework/components/uart/

### INCOMPLETE - Missing APB Wrappers or Core RTL

| Module | Directory Exists | RTL Status | APB Wrapper | Priority |
|--------|------------------|------------|-------------|----------|
| **DMA_8237** | No | No | No | LOW (use Stream DMA instead) |
| **PS2** | No | No | No | LOW |
| **FDC** | No | No | No | LOW |

### EXTERNAL REFERENCE - Modern High-Performance Blocks

For modern DMA functionality, use the Stream DMA project instead of 8237:

| Module | Location | Description |
|--------|----------|-------------|
| **Stream DMA** | projects/components/stream/ | Modern AXI-based descriptor DMA engine |

The Stream DMA provides:
- Descriptor-based operation
- AXI4 master read/write engines
- Multi-channel support
- High-performance streaming

### 🟣 SPECIAL - Integration/Support Modules

| Module | Purpose | Status |
|--------|---------|--------|
| **rlb_top** | Top-level integration | 📋 Planned |
| **apb_xbar** | APB crossbar | ✅ Exists |

---

## Validation Status

### Test Infrastructure Existing

**HPET:**
- ✅ `dv/tests/hpet/test_apb_hpet.py` - Cocotb tests exist
- Status: Has comprehensive validation

**PIT_8254:**
- ✅ `dv/tests/pit_8254/test_apb_pit_8254.py` - Cocotb tests exist
- Status: Has comprehensive validation

**RTC:**
- ✅ `dv/tests/rtc/test_apb_rtc.py` - Cocotb test runner
- ✅ `dv/tbclasses/rtc/rtc_tb.py` - Testbench class
- ✅ `dv/tbclasses/rtc/rtc_tests_basic.py` - Basic tests
- Status: Has comprehensive validation infrastructure

### Test Infrastructure NEEDED

**PIC_8259:**
- ❌ No tests in `dv/tests/pic_8259/`
- ❌ No testbench classes
- ✅ Has helper: `rtl/pic_8259/pic_8259_helper.py`
- **TODO:** Create basic Cocotb tests

**SMBus:**
- ❌ No tests in `dv/tests/smbus/`
- ❌ No testbench classes
- ✅ Has helper: `rtl/smbus/smbus_helper.py`
- **TODO:** Create comprehensive Cocotb test suite
  - Physical layer tests (I2C signaling)
  - Transaction type tests
  - FIFO tests
  - PEC validation
  - Timeout tests

**PM_ACPI:**
- ❌ No tests in `dv/tests/pm_acpi/`
- ❌ No testbench classes
- ❌ No helper script yet
- **TODO (per TODO.md):**
  - Create `pm_acpi_helper.py`
  - Basic register R/W tests
  - PM timer increment/overflow tests
  - Power state transition tests
  - GPE event tests
  - Clock gating tests
  - Wake event tests

**IOAPIC:**
- ❌ No tests in `dv/tests/ioapic/`
- ❌ No testbench classes
- ❌ No helper script yet
- **TODO (per TODO.md):**
  - Create `ioapic_helper.py`
  - Indirect register access tests (IOREGSEL/IOWIN)
  - IRQ edge-triggered tests
  - IRQ level-triggered tests
  - Polarity tests (active high/low)
  - Priority arbitration tests
  - Remote IRR tests
  - Delivery status tests
  - EOI handling tests

---

## Detailed Work Remaining

### Phase 1: Validation Infrastructure (High Priority 🔴)

#### 1. PIC_8259 Validation
**Estimated Time:** 2-3 days

- [ ] Create `dv/tests/pic_8259/` directory
- [ ] Create `test_apb_pic_8259.py` Cocotb test runner
- [ ] Create `dv/tbclasses/pic_8259/` directory
- [ ] Create `pic_8259_tb.py` testbench class
- [ ] Create `pic_8259_tests_basic.py` basic tests
- [ ] Test IRQ handling, priority, masking, EOI

#### 2. SMBus Validation
**Estimated Time:** 5-7 days

- [ ] Create `dv/tests/smbus/` directory
- [ ] Create `test_apb_smbus.py` Cocotb test runner
- [ ] Create `dv/tbclasses/smbus/` directory
- [ ] Create `smbus_tb.py` testbench class
- [ ] Create SMBus protocol monitor/driver
- [ ] Test all transaction types:
  - [ ] Quick Command
  - [ ] Send/Receive Byte
  - [ ] Write/Read Byte Data
  - [ ] Write/Read Word Data
  - [ ] Block Write/Read
- [ ] Test PEC functionality
- [ ] Test timeout handling
- [ ] Test arbitration and clock stretching
- [ ] Test FIFO operations

#### 3. PM_ACPI Validation
**Estimated Time:** 5-7 days

- [ ] Create `pm_acpi_helper.py` (based on smbus_helper.py)
- [ ] Create `dv/tests/pm_acpi/` directory
- [ ] Create `test_apb_pm_acpi.py` Cocotb test runner
- [ ] Create `dv/tbclasses/pm_acpi/` directory
- [ ] Create `pm_acpi_tb.py` testbench class
- [ ] Test PM timer operation and overflow
- [ ] Test power state transitions (S0↔S1↔S3)
- [ ] Test GPE event handling
- [ ] Test clock gating control
- [ ] Test power domain control
- [ ] Test wake event functionality
- [ ] Test interrupt aggregation

#### 4. IOAPIC Validation
**Estimated Time:** 5-7 days

- [ ] Create `ioapic_helper.py`
- [ ] Create `dv/tests/ioapic/` directory
- [ ] Create `test_apb_ioapic.py` Cocotb test runner
- [ ] Create `dv/tbclasses/ioapic/` directory
- [ ] Create `ioapic_tb.py` testbench class
- [ ] Test indirect register access (IOREGSEL/IOWIN)
- [ ] Test all 24 IRQ inputs
- [ ] Test edge-triggered interrupts
- [ ] Test level-triggered interrupts
- [ ] Test polarity (active high/low)
- [ ] Test priority arbitration
- [ ] Test Remote IRR management
- [ ] Test EOI handling
- [ ] Test delivery status
- [ ] Test redirection table configuration

**Total Validation Time:** 17-24 days

---

### Phase 2: Missing Modules Implementation (Medium-High Priority)

#### 5. GPIO (General Purpose I/O)
**Estimated Time:** 2-3 days

- [ ] Create `gpio/` directory structure
- [ ] PeakRDL register specification
  - Direction control (input/output per pin)
  - Output data register
  - Input data register (read-only)
  - Pull-up/pull-down control
  - Interrupt enable per pin
  - Edge/level trigger configuration
  - Interrupt status (W1C)
- [ ] `gpio_core.sv` implementation
- [ ] `gpio_config_regs.sv` with PeakRDL
- [ ] `apb_gpio.sv` wrapper
- [ ] Validation suite

**Typical Configuration:**
- 32-bit GPIO ports
- Per-pin direction control
- Interrupt on change
- Debouncing (optional)

#### 6. UART_16550 (Serial Port)
**Estimated Time:** 4-6 days

- [ ] Create `uart_16550/` directory structure
- [ ] PeakRDL register specification (16550 compatible)
  - TX/RX data registers
  - Interrupt enable/identification
  - FIFO control
  - Line control (data bits, stop bits, parity)
  - Modem control/status
  - Divisor latch for baud rate
  - Scratch register
- [ ] `uart_16550_core.sv` implementation
  - TX/RX state machines
  - Baud rate generator
  - FIFO buffers
  - Interrupt generation
- [ ] `uart_16550_config_regs.sv` with PeakRDL
- [ ] `apb_uart_16550.sv` wrapper
- [ ] Validation suite with UART protocol monitoring

**16550 Features:**
- 16-byte TX/RX FIFOs
- Programmable baud rate
- Interrupt on: RX data, TX empty, line status, modem status
- Compatible with PC serial ports

#### 7. DMA Controller
**Estimated Time:** 5-8 days

- [ ] Create `dma/` directory structure
- [ ] PeakRDL register specification
  - Channel configuration (multiple channels)
  - Source/destination addresses
  - Transfer count
  - Control (start, stop, pause)
  - Status (busy, complete, error)
  - Interrupt enables
- [ ] `dma_core.sv` implementation
  - Multi-channel arbitration
  - AXI master interface for transfers
  - Descriptor engine
  - Scatter-gather support
- [ ] `dma_config_regs.sv` with PeakRDL
- [ ] `apb_dma.sv` wrapper
- [ ] Validation suite

**Estimated Implementation Time for Missing Modules:** 11-17 days

---

### Phase 3: Integration and System Validation

#### RLB Top-Level Integration
**Estimated Time:** 3-5 days

- [ ] Design `rlb_top.sv` integration module
- [ ] Instantiate all RLB peripherals
- [ ] APB crossbar integration
- [ ] Address map definition
- [ ] Interrupt aggregation
- [ ] System-level validation
- [ ] Full SoC integration tests

---

## Validation Roadmap Summary

### Immediate Priorities (Next 4 Weeks)

**Week 1-2: New Module Validation**
- Day 1-3: PIC_8259 test suite
- Day 4-7: SMBus test suite (complex)
- Day 8-10: PM_ACPI test suite

**Week 3-4: New Module Validation Continued**
- Day 11-14: IOAPIC test suite (complex)
- Day 15-17: Regression testing all modules
- Day 18-20: Integration testing

### Medium Term (Month 2)

**Weeks 5-6: GPIO Implementation**
- Design, implement, validate GPIO module

**Weeks 7-8: UART_16550 Implementation**
- Design, implement, validate 16550 UART

### Long Term (Month 3+)

**Month 3: DMA and Advanced Features**
- DMA controller implementation
- Advanced features for existing modules
- Performance optimization

**Month 4: System Integration**
- rlb_top implementation
- Full SoC validation
- Hardware bring-up preparation

---

## Architectural Compliance Status

### ✅ All Active Modules Compliant

**Standard Pattern:**
```
APB → apb_slave[_cdc] → CMD/RSP → peakrdl_to_cmdrsp →  
  → <module>_regs (PeakRDL) → hwif → <module>_core
```

**Verified Modules (7/7):**
1. ✅ HPET - Reference implementation
2. ✅ PIT_8254 - Fully compliant
3. ✅ RTC - Fully compliant
4. ✅ PIC_8259 - Fully compliant
5. ✅ SMBus - Fully compliant (completed this session)
6. ✅ PM_ACPI - Fully compliant (completed this session)
7. ✅ IOAPIC - Fully compliant (completed this session)

**Architecture Audit Result:** **100% COMPLIANT** ✅

---

## Python Helper Scripts Status

| Module | Helper Script | Status |
|--------|---------------|--------|
| HPET | N/A | Not typically needed |
| PIT_8254 | N/A | Simple register access |
| RTC | ✅ rtc_helper.py | Complete |
| PIC_8259 | ✅ pic_8259_helper.py | Complete |
| SMBus | ✅ smbus_helper.py | Complete |
| PM_ACPI | ❌ | **NEEDED** |
| IOAPIC | ❌ | **NEEDED** |
| GPIO | ❌ | Future |
| UART_16550 | ❌ | Future |
| DMA | ❌ | Future |

**Actions Needed:**
- [ ] Create `pm_acpi_helper.py` - Power state, timer, GPE, clock gate utilities
- [ ] Create `ioapic_helper.py` - Indirect access, redirection table utilities

---

## Documentation Status

| Module | README | TODO.md | IMPL_STATUS.md | PeakRDL Docs |
|--------|--------|---------|----------------|--------------|
| HPET | ✅ Good | ❌ | ❌ | ✅ |
| PIT_8254 | ✅ Good | ❌ | ❌ | ✅ |
| RTC | ✅ Good | ❌ | ❌ | ✅ |
| PIC_8259 | ✅ Good | ❌ | ❌ | ✅ |
| SMBus | ✅ Excellent | ✅ | ✅ | ✅ |
| PM_ACPI | ⚠️ Basic | ✅ Excellent | ❌ | ✅ |
| IOAPIC | ⚠️ Basic | ✅ Excellent | ❌ | ✅ |

**Actions Needed:**
- [ ] Update PM_ACPI README.md with full details
- [ ] Update IOAPIC README.md with full details
- [ ] Create IMPLEMENTATION_STATUS.md for PM_ACPI
- [ ] Create IMPLEMENTATION_STATUS.md for IOAPIC
- [ ] Add TODO.md to older modules (HPET, PIT, RTC, PIC)

---

## Work Breakdown - Estimated Time

### Immediate (Next Sprint - 3-4 Weeks)

**Validation (17-24 days):**
- PIC_8259 tests: 2-3 days
- SMBus tests: 5-7 days
- PM_ACPI tests: 5-7 days
- IOAPIC tests: 5-7 days

**Documentation (3-4 days):**
- Python helpers: 1-2 days (PM_ACPI, IOAPIC)
- README updates: 1 day
- IMPLEMENTATION_STATUS: 1 day

**Total Immediate:** ~20-28 days (4-6 weeks)

### Short Term (Next Quarter - Weeks 5-12)

**New Module Implementation (22-34 days):**
- GPIO: 2-3 days RTL + 2-3 days validation = 4-6 days
- UART_16550: 4-6 days RTL + 3-5 days validation = 7-11 days
- DMA: 5-8 days RTL + 6-9 days validation = 11-17 days

**Total Short Term:** ~22-34 days (5-7 weeks)

### Medium Term (Quarter 2 - Weeks 13-24)

**System Integration (15-25 days):**
- rlb_top design and implementation: 3-5 days
- Address map finalization: 1-2 days
- Interrupt routing integration: 2-3 days
- System-level tests: 5-10 days
- Full regression: 4-5 days

**Total Medium Term:** ~15-25 days (3-5 weeks)

### Long Term (Quarter 3+)

**Advanced Features:**
- Enhanced power management
- Advanced DMA modes
- Multi-processor support
- Legacy PC compatibility mode
- Performance optimization
- Area optimization

---

## Critical Path Items

### For MVP System (Minimum Viable Product)

**Must Have:**
1. ✅ HPET - Timer subsystem
2. ✅ PIT_8254 - Legacy timer
3. ✅ RTC - Real-time clock
4. ✅ PIC_8259 - Legacy interrupts
5. ❌ GPIO - I/O control
6. ❌ UART_16550 - Serial communication

**Should Have:**
7. ✅ SMBus - System management
8. ❌ DMA - Data transfers
9. ✅ IOAPIC - Advanced interrupts
10. ✅ PM_ACPI - Power management

**Nice to Have:**
- PS/2 controller
- Floppy disk controller
- Additional timers
- Watchdog timer

### Critical for Validation

**Blocking Items:**
- SMBus physical layer validation (complex protocol)
- PM_ACPI power state transitions
- IOAPIC indirect register access
- Multi-module interrupt integration

**Non-Blocking:**
- Documentation polish
- Advanced feature testing
- Performance characterization

---

## Recommendations

### Next Actions (Priority Order)

1. **Create Python Helpers** (2 days)
   - pm_acpi_helper.py
   - ioapic_helper.py

2. **Validate Recently Completed Modules** (17-24 days)
   - PIC_8259 tests (quick win)
   - SMBus tests (critical, complex)
   - PM_ACPI tests (medium complexity)
   - IOAPIC tests (high complexity)

3. **Implement Critical Missing Modules** (11-17 days)
   - GPIO (essential for I/O)
   - UART_16550 (essential for debug/communication)
   - DMA (important for performance)

4. **System Integration** (15-25 days)
   - rlb_top integration
   - Full system validation
   - Address map documentation

**Total to MVP:** ~45-68 days (9-14 weeks, ~2-3 months)

---

## Session Summary (2025-11-16)

**Completed Today:**
- ✅ PM_ACPI: Full implementation (registers, core, wrapper, docs)
- ✅ IOAPIC: Full implementation (registers, core, wrapper, docs)
- ✅ Both modules pushed to repository

**Delivered:** ~3000+ lines of production RTL, 2 complete RLB modules

**Architecture:** 100% compliant with RLB methodology

---

**Last Updated:** 2025-11-16  
**Next Priority:** Validation infrastructure for newly completed modules
