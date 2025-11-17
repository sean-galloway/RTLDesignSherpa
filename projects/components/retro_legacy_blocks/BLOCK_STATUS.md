# Retro Legacy Blocks - Development Status

**Last Updated:** 2025-11-16

---

## Block Status Overview

| Block | Module Name | Priority | Status | RTL | Tests | Docs | Address |
|-------|-------------|----------|--------|-----|-------|------|---------|
| HPET | `apb_hpet` | High | ✅ Complete | ✅ | ✅ 5/6 100% | ✅ | 0x4000_0000-0x0FFF |
| 8259 PIC | `apb_pic_8259` | High | 🔧 In Progress | 🔧 | 🔧 3/6 50% | ❌ | 0x4000_1000-0x1FFF |
| 8254 PIT | `apb_pit_8254` | High | ✅ Complete | ✅ | ✅ 6/6 100% | ✅ | 0x4000_2000-0x2FFF |
| RTC | `apb_rtc` | Medium | ✅ Complete | ✅ | ✅ 6/6 100% | ✅ | 0x4000_3000-0x3FFF |
| SMBus | `apb_smbus` | Medium | 🔧 RTL Done | ✅ | ❌ | ❌ | 0x4000_4000-0x4FFF |
| PM/ACPI | `apb_pm_acpi` | Medium | 🔧 RTL Done | ✅ | ❌ | ❌ | 0x4000_5000-0x5FFF |
| IOAPIC | `apb_ioapic` | Medium | 🔧 In Progress | 🔧 | 🔧 3/6 50% | ❌ | 0x4000_6000-0x6FFF |
| GPIO | `apb_gpio` | Medium | 📋 Future | ❌ | ❌ | ❌ | TBD |
| UART | `apb_uart` | Medium | 📋 Future | ❌ | ❌ | ❌ | TBD |
| SPI | `apb_spi` | Low | 📋 Future | ❌ | ❌ | ❌ | TBD |
| I2C | `apb_i2c` | Low | 📋 Future | ❌ | ❌ | ❌ | TBD |
| Watchdog | `apb_watchdog` | Low | 📋 Future | ❌ | ❌ | ❌ | TBD |
| Interconnect | `apb_interconnect` | Low | 📋 Future | ❌ | ❌ | ❌ | 0x4000_F000-0xFFFF |

---

## Directory Structure Status

### HPET (✅ Production Ready)
```
✅ rtl/hpet/                    - Complete RTL implementation
✅ dv/tbclasses/hpet/           - Complete testbench classes
✅ dv/tests/hpet/               - Complete test suite
✅ docs/hpet_spec/              - Complete specification
```

### 8259 PIC (📋 Structure Created)
```
📋 rtl/pic_8259/                - Directory created, README added
  ├── peakrdl/                 - Empty (SystemRDL to be added)
  └── filelists/               - Empty (filelists to be added)
📋 dv/tbclasses/pic_8259/       - Directory created, README added
📋 dv/tests/pic_8259/           - Directory created, README added
📋 docs/pic_8259_spec/          - Directory created, README added
```

### 8254 PIT (📋 Structure Created)
```
📋 rtl/pit_8254/                - Directory created, README added
  ├── peakrdl/                 - Empty (SystemRDL to be added)
  └── filelists/               - Empty (filelists to be added)
📋 dv/tbclasses/pit_8254/       - Directory created, README added
📋 dv/tests/pit_8254/           - Directory created, README added
📋 docs/pit_8254_spec/          - Directory created, README added
```

### RTC (📋 Structure Created)
```
📋 rtl/rtc/                     - Directory created, README added
  ├── peakrdl/                 - Empty (SystemRDL to be added)
  └── filelists/               - Empty (filelists to be added)
📋 dv/tbclasses/rtc/            - Directory created, README added
📋 dv/tests/rtc/                - Directory created, README added
📋 docs/rtc_spec/               - Directory created, README added
```

### SMBus (📋 Structure Created)
```
📋 rtl/smbus/                   - Directory created, README added
  ├── peakrdl/                 - Empty (SystemRDL to be added)
  └── filelists/               - Empty (filelists to be added)
📋 dv/tbclasses/smbus/          - Directory created, README added
📋 dv/tests/smbus/              - Directory created, README added
📋 docs/smbus_spec/             - Directory created, README added
```

### PM/ACPI (📋 Structure Created)
```
📋 rtl/pm_acpi/                 - Directory created, README added
  ├── peakrdl/                 - Empty (SystemRDL to be added)
  └── filelists/               - Empty (filelists to be added)
📋 dv/tbclasses/pm_acpi/        - Directory created, README added
📋 dv/tests/pm_acpi/            - Directory created, README added
📋 docs/pm_acpi_spec/           - Directory created, README added
```

### IOAPIC (📋 Structure Created)
```
📋 rtl/ioapic/                  - Directory created, README added
  ├── peakrdl/                 - Empty (SystemRDL to be added)
  └── filelists/               - Empty (filelists to be added)
📋 dv/tbclasses/ioapic/         - Directory created, README added
📋 dv/tests/ioapic/             - Directory created, README added
📋 docs/ioapic_spec/            - Directory created, README added
```

---

## Development Checklist Per Block

For each block to reach production-ready status:

### RTL Development
- [ ] Create SystemRDL register specification in `peakrdl/`
- [ ] Generate register RTL using PeakRDL
- [ ] Implement core logic (`{block}_core.sv`)
- [ ] Create APB wrapper (`apb_{block}.sv`)
- [ ] Add reset macros (use `ALWAYS_FF_RST`)
- [ ] Add FPGA synthesis attributes
- [ ] Create filelists for component and integration
- [ ] Verify lint-clean (Verilator)

### Testbench Development
- [ ] Create main testbench class (`{block}_tb.py`)
- [ ] Implement mandatory methods (setup/assert/deassert)
- [ ] Create basic test suite (4-6 tests)
- [ ] Create medium test suite (5-8 tests)
- [ ] Create full test suite (3-5 tests)
- [ ] Create test runner (`test_apb_{block}.py`)
- [ ] Create pytest configuration (`conftest.py`)
- [ ] Achieve 100% pass rate on basic/medium
- [ ] Achieve ≥95% pass rate on full

### Documentation
- [ ] Write Chapter 1: Overview
- [ ] Write Chapter 2: Block Diagrams
- [ ] Write Chapter 3: Interfaces
- [ ] Write Chapter 4: Programming Guide
- [ ] Write Chapter 5: Register Map
- [ ] Create integration examples
- [ ] Document known issues

---

## Next Steps

### Immediate (Q1 2026)
1. **8259 PIC** - Start with register specification
2. **8254 PIT** - Start with counter mode logic
3. **RTC** - Start with time counter logic

### Near-Term (Q2 2026)
4. **GPIO** - Create directory structure
5. **SMBus** - Continue from 8259/8254 patterns
6. **PM/ACPI** - Design power sequencing logic

### Mid-Term (Q3-Q4 2026)
7. **IOAPIC** - Design interrupt routing logic
8. **UART** - 16550-compatible implementation
9. **SPI/I2C/Watchdog** - Lower priority blocks

### Long-Term (2027)
10. **Interconnect** - ID/Version registers
11. **RLB Wrapper** - Integrate all blocks
12. **System Integration** - Complete example designs

---

## RLB Wrapper Integration Checklist

When all blocks are complete:

- [ ] Create `rtl/rlb_wrapper/` directory
- [ ] Implement APB decoder (4KB window decode)
- [ ] Instantiate all block modules
- [ ] Create error slave for unmapped addresses
- [ ] Aggregate interrupts from all blocks
- [ ] Create top-level testbench
- [ ] Verify address decode correctness
- [ ] Test all blocks through wrapper
- [ ] Document integration guide
- [ ] Create FPGA reference design

---

**Legend:**
- ✅ Complete
- 📋 Planned (structure created)
- ❌ Not started
- 🔧 In progress

**Version:** 1.0
**Maintained By:** RTL Design Sherpa Project
